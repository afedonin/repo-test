/* -*-pgsql-c-*- */
/*
 * $Header$
 *
 * pgpool: a language independent connection pool server for PostgreSQL
 * written by Tatsuo Ishii
 *
 * Copyright (c) 2003-2010	PgPool Global Development Group
 *
 * Permission to use, copy, modify, and distribute this software and
 * its documentation for any purpose and without fee is hereby
 * granted, provided that the above copyright notice appear in all
 * copies and that both that copyright notice and this permission
 * notice appear in supporting documentation, and that the name of the
 * author not be used in advertising or publicity pertaining to
 * distribution of the software without specific, written prior
 * permission. The author makes no representations about the
 * suitability of this software for any purpose.  It is provided "as
 * is" without express or implied warranty.
 *
 * pool_rewrite_query.c: rewrite_query
 *
 */

#include "pool.h"
#include "pool_config.h"
#include "pool_rewrite_query.h"
#include "pool_proto_modules.h"
#include "pool_session_context.h"

#include <string.h>
#include <errno.h>
#include <stdlib.h>

static int getInsertRule(ListCell *lc,List *list_t ,DistDefInfo *info, int div_key_num);
static void examInsertStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message);
static void examSelectStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message, bool init_is_loadbalance);

static void examInTransactionStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message,char *query);
static void examReplicationFetchStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message,char *query);
static void examDistributedFetchStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message,char *query,bool need_node_id,List* node_ids,List* node_counts,int offset,int limit);

static char *delimistr(char *str);
static int direct_parallel_query(RewriteQuery *message);
static void initMessage(RewriteQuery *message);
static void initdblink(ConInfoTodblink *dblink, POOL_CONNECTION_POOL *backend);
static void analyze_debug(RewriteQuery *message);

static char *escape_string2(char *str)
{
	int len = strlen(str), i, j;
	char *es = palloc0(len * 2 + 1);

	if (es == NULL)
	{
		return NULL;
	}

	for (i = 0, j = 0; i < len; i++, j++)
	{
		if (str[i] == '\'')
		{
			es[j++] = '\'';
		}
		else if (str[i] == '\\')
		{
			es[j++] = '\\';
		}
		else if (str[i] == '\"')
		{
			es[j++] = '\"';
		}
		es[j] = str[i];
	}

	return es;
}

/* create error message  */
char *pool_error_message(char *message)
{
	String *str;

	str = init_string("");
	string_append_char(str,message);
	return str->data;
}

/*
 *  search DistDefInfo(this info is build in starting process
 *  and get node id where a query send.
 */
static int getInsertRule(ListCell *lc,List *list_t ,DistDefInfo *info,int div_key_num)
{
	int loop_counter = 0;
	int node_number = -1;
	ListCell *cell;

	if(list_t->length != 1)
		return -1;

	cell = list_head(list_t);

	if(!cell && !IsA(cell,List))
		return 1;

	foreach(lc,lfirst(cell))
	{
		A_Const *constant;
		Value value;
		void *obj = NULL;

		obj = lfirst(lc);

		/* it supports casting syntax such as "A::B::C" */
		while (obj && IsA(obj, TypeCast))
		{
			TypeCast *type = (TypeCast *) obj;
			obj = type->arg;
		}

		if(!obj || !IsA(obj, A_Const))
			return -1;

		if (loop_counter == div_key_num)
		{
			constant = (A_Const *) obj;
			value = constant->val;
			if (value.type == T_Integer)
			{
				char temp[16];
				sprintf(temp,"%ld",value.val.ival);
				node_number = pool_get_id(info,temp);
				break;
			}
			else
			{
				if(value.val.str)
					node_number = pool_get_id(info, value.val.str);
				else
					return -1;
				break;
			}
		}
		loop_counter++;
	}
	/* if node_number is -1, cannot get return value from pool_get_id() */
	return node_number;
}

/*
 * This function processes the decision whether to
 * distribute the insert sentence to the node.
 */
static void examInsertStmt(Node *node,POOL_CONNECTION_POOL *backend, RewriteQuery *message)
{
	RangeVar *table;
	int cell_num;
	int node_number;
	DistDefInfo *info = NULL;
	ListCell *lc = NULL;
	List *list_t = NULL;
	int div_key_num = 0;
	int dist_def_flag = 0;
	InsertStmt *insert = (InsertStmt *) node;

	message->type = node->type;

	/* insert target table */
	table = insert->relation;
	if (!table)
	{
		/* send  error message to frontend */
		message->r_code = INSERT_SQL_RESTRICTION;
		message->r_node = -1;
		message->rewrite_query = pool_error_message("cannot find table name");
		return;
	}

	/* pool_debug("exam_InsertStmt insert table_name %s:",table->relname); */

	info = pool_get_dist_def_info(MASTER_CONNECTION(backend)->sp->database,
								  table->schemaname,
								  table->relname);

	if (!info)
	{
		/* send  error message to frontend */
		message->r_code = INSERT_DIST_NO_RULE;
		return;
	}

	/* the source SELECT ? */
	if (insert->selectStmt && ((SelectStmt *)insert->selectStmt)->targetList)
	{
		/* send  error message to frontend */
		message->r_code = INSERT_SQL_RESTRICTION;
		message->r_node = -1;
		message->rewrite_query = pool_error_message("cannot use SelectStmt in InsertStmt");
		return;
	}

	list_t = (List *)(((SelectStmt *)insert->selectStmt)->valuesLists);

	if (!list_t)
	{
		/* send  error message to frontend */
		message->r_code = INSERT_SQL_RESTRICTION;
		message->r_node = -1;
		message->rewrite_query = pool_error_message("cannot find target List");
		return;
	}

	/* number of target list */

	if(list_t->length == 1 && IsA(lfirst(list_head(list_t)),List))
	{
		cell_num = ((List *) lfirst(list_head(list_t)))->length;
	}
	else
	{
			/* send  error message to frontend */
			message->r_code = INSERT_SQL_RESTRICTION;
			message->r_node = -1;
			message->rewrite_query = pool_error_message("cannot analzye this InsertStmt");
			return;
  }


	/* Is the target columns ?*/
	if (!insert->cols)
	{
		div_key_num = info->dist_key_col_id;
		dist_def_flag = 1;

		pool_debug("cell number %d, div key num %d, div_key columname %s",cell_num,div_key_num,info->col_list[div_key_num]);

		if (cell_num < div_key_num)
		{
			/* send  error message to frontend */
			message->r_code = INSERT_SQL_RESTRICTION;
			message->r_node = -1;
			message->rewrite_query = pool_error_message("cannot find dividing key in InsertStmt");
			return;
		}

  }
	else
	{
		List *list_cols = (List *) insert->cols;

		foreach(lc, list_cols)
		{
			Node *n;
			ResTarget *target;
 			n = lfirst(lc);
			target = (ResTarget *) n;
			if (strcmp(target->name,info->dist_key_col_name) == 0)
			{
				dist_def_flag = 1;
				break;
			}
			div_key_num++;
		}

		if (cell_num < div_key_num)
		{
			/* send  error message to frontend */
			message->r_code = INSERT_SQL_RESTRICTION;
			message->r_node = -1;
			message->rewrite_query = pool_error_message("cannot find dividing key in InsertStmt");
			return;
		}
	}

	if (dist_def_flag != 1)
	{
		/* send  error message to frontend */
		message->r_code = INSERT_SQL_RESTRICTION;
		message->r_node = -1;
		message->rewrite_query = pool_error_message("cannot find dividing key in InsertStmt");
		return;
	}

	/* this loop get insert one args of divide rule */
	node_number = getInsertRule(lc, list_t, info, div_key_num);

	if (node_number < 0)
	{
		/* send  error message to frontend */
		message->r_code = INSERT_SQL_RESTRICTION;
		message->r_node = -1;
		message->rewrite_query = pool_error_message("cannot get node_id from system db");
		return;
	}

	pool_debug("insert node_number =%d",node_number);
	message->r_code = 0;
	message->r_node = node_number;
	message->rewrite_query = nodeToString(node);
}

/* start of rewriting query */
static void examSelectStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message, bool init_is_loadbalance)
{
	static ConInfoTodblink dblink;

	/* initialize dblink info */
	initdblink(&dblink,backend);

	/* initialize  message */
	initMessage(message);
	message->type = node->type;
	message->r_code = SELECT_DEFAULT;
	message->is_loadbalance = init_is_loadbalance;

  /* do rewrite query */
	nodeToRewriteString(message,&dblink,node);
}

static void examInTransactionStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message,char *query)
{
	String *str;
	str = init_string("");

	string_append_char(str, "SELECT dblink_exec('transaction_conn','SELECT pool_transaction(\"");
	string_append_char(str, escape_string2( query ));
	string_append_char(str, "\")')");

	message->rewrite_query = str->data;
	message->type = node->type;
}

static void examReplicationFetchStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message,char *query)
{
	String *str;
	str = init_string("");

	FetchStmt *stmt = (FetchStmt *)node;
	CursorsInfo* curinfo = pool_session_get_cursor_info(stmt->portalname);

	string_append_char(str, "SELECT * FROM dblink('transaction_conn','SELECT pool_transaction(\"");
	string_append_char(str, escape_string2( query ));
	string_append_char(str, "\")')");
	if( curinfo )
	{
		string_append_char(str, curinfo->footer_info);
	}

	message->rewrite_query = str->data;
	message->type = node->type;
}

static void examDistributedFetchStmt(Node *node,POOL_CONNECTION_POOL *backend,RewriteQuery *message,char *query,bool need_node_id,List* node_ids,List* node_counts,int offset,int limit)
{
	String *str;
	str = init_string("");

	FetchStmt *stmt = (FetchStmt *)node;
	CursorsInfo* curinfo = pool_session_get_cursor_info(stmt->portalname);

	if (stmt->ismove)
	{
		string_append_char(str, "SELECT dblink_exec('transaction_conn','SELECT pool_move(\"");
	}
	else
	{
		string_append_char(str, "SELECT * FROM dblink('transaction_conn','SELECT pool_move(\"");
	}

	string_append_char(str, escape_string2( /*query*/nodeToString(node) ));
	string_append_char(str, "\"");

	string_append_char(str, need_node_id ? ",\"1\"" : ",\"0\"");

	ListCell* node_id_cell; ListCell* node_count_cell = list_head(node_counts);
	foreach(node_id_cell, node_ids)
	{
		char node_id[16], node_count[64];
		snprintf(node_id, 16, "%d", lfirst_int(node_id_cell));
		snprintf(node_count, 64, "%ld", (long)lfirst(node_count_cell));

		string_append_char(str, ",\"");
		string_append_char(str, node_id);
		string_append_char(str, "\",\"");
		string_append_char(str, node_count);
		string_append_char(str, "\"");

		node_count_cell = lnext(node_count_cell);
	}

	string_append_char(str, ")')");

	if( !stmt->ismove && curinfo )
	{
		if( need_node_id )
		{
			char *p_bracket = strchr(curinfo->footer_info, '(');
			if (p_bracket)
			{
				++p_bracket;
				char buf[128];
				strncpy(buf, curinfo->footer_info, p_bracket - curinfo->footer_info);
				buf[p_bracket - curinfo->footer_info] = '\0';
				string_append_char(str, buf);
				string_append_char(str, NODE_ID_COLUMN_NAME);
				string_append_char(str, " integer,");
				string_append_char(str, p_bracket);
			}
		}
		else
		{
			string_append_char(str, curinfo->footer_info);
		}

		if (limit)
		{
			char buf[128];
			snprintf(buf, 128, "%d", limit);
			string_append_char(str, " LIMIT ");
			string_append_char(str, buf);
		}

		if (offset)
		{
			char buf[128];
			snprintf(buf, 128, "%d", offset);
			string_append_char(str, " OFFSET ");
			string_append_char(str, buf);
		}
	}

	message->rewrite_query = str->data;
	message->type = node->type;
}

/* initialize Message */
static void initMessage(RewriteQuery *message)
{
	message->r_code = 0;
	message->r_node = 0;
	message->column = 0;
	message->virtual_num = 0;
	message->is_pg_catalog = false;
	message->is_loadbalance = false;
	message->is_parallel = false;

	message->is_reflected = false;
	message->is_target_select = false;
	message->special_info = false;
	message->is_cursor_move = false;
	message->in_quote_block = false;
	message->in_union = false;

	message->table_relname = NULL;
	message->table_alias = NULL;
	message->dbname = NULL;
	message->schemaname = NULL;
	message->rewrite_query = NULL;
	message->rewritelock = -1;
	message->ignore_rewrite = -1;
	message->ret_num = 0;
}

/* set dblink info */
static void initdblink(ConInfoTodblink *dblink,POOL_CONNECTION_POOL *backend)
{
	dblink->dbname =  MASTER_CONNECTION(backend)->sp->database;
	dblink->hostaddr = pool_config->pgpool2_hostname;
	dblink->user = MASTER_CONNECTION(backend)->sp->user;
	dblink->port = pool_config->port;
	dblink->password = MASTER_CONNECTION(backend)->con->password;
}

/* reference of pg_catalog or not */
int IsSelectpgcatalog(Node *node,POOL_CONNECTION_POOL *backend)
{
	static ConInfoTodblink dblink;
	static RewriteQuery message;

	/* initialize dblink info */
	initdblink(&dblink,backend);

	/* initialize  message */
	initMessage(&message);

	message.type = node->type;

	initdblink(&dblink,backend);

	if(message.is_pg_catalog)
	{
		pool_debug("Isselectpgcatalog %d",message.is_pg_catalog);
		return 1;
	}
	else
	{
		return 0;
	}
}

/*
 *  SELECT statement or INSERT statement is special,
 *  peculiar process is needed in parallel mode.
 */
RewriteQuery *rewrite_query_stmt(Node *node, POOL_CONNECTION *frontend, POOL_CONNECTION_POOL *backend, RewriteQuery *message, POOL_QUERY_CONTEXT *query_context)
{
	switch(node->type)
	{
		case T_SelectStmt:
		{
			SelectStmt *stmt = (SelectStmt *)node;

			 /* Because "SELECT INTO" cannot be used in a parallel mode,
			  * the error message is generated and send "ready for query" to frontend.
			  */
			if(stmt->intoClause)
			{
				pool_send_error_message(frontend, MAJOR(backend), "XX000",
										"pgpool2 sql restriction",
										"cannot use select into ...", "", __FILE__,
										__LINE__);


				pool_send_readyforquery(frontend);
				message->status=POOL_CONTINUE;
				break;
			}

			/*
			 * The Query is actually rewritten based on analytical information on the Query.
			 */
			examSelectStmt(node,backend,message,query_context->is_loadbalance);

			if (message->r_code != SELECT_PGCATALOG &&
				message->r_code != SELECT_RELATION_ERROR)
			{
				/*
				 * The rewritten Query is transmitted to system db,
				 * and execution status is received.
				 */
				POOL_CONNECTION_POOL_SLOT *system_db = pool_system_db_connection();
				message->status = OneNode_do_command(frontend,
													system_db->con,
													message->rewrite_query,
													backend->info->database,
													true,
													false,
													0);
			}
			else
			{
				if(TSTATE(backend, MASTER_NODE_ID) == 'T' &&
				   message->r_code == SELECT_RELATION_ERROR)
				{
					/*
					 * In the case of message->r_code == SELECT_RELATION_ERROR and in the transaction,
					 * Transmit the Query to all back ends, and to abort transaction.
					 */
					pool_debug("pool_rewrite_stmt(select): Inside transaction. abort transaction");
					message->rewrite_query = nodeToString(node);
					message->status = pool_parallel_exec(frontend,backend,message->rewrite_query,node,true, query_context);
				}
				else
				{
					/*
					 * Ohter cases of message->r_code == SELECT_RELATION_ERROR
					 * or SELECT_PG_CATALOG,
					 * Transmit the Query to Master node and receive status.
					 */
					pool_debug("pool_rewrite_stmt: executed by Master");
					message->rewrite_query = nodeToString(node);
					message->status = OneNode_do_command(frontend,
														MASTER(backend),
														message->rewrite_query,
															backend->info->database,
															true,
															false,
															0);
				}
			}
			pool_debug("pool_rewrite_stmt: select message_code %d",message->r_code);
		}
		break;

		case T_InsertStmt:

			if (pool_get_session_context()->in_transaction)
			{
				String *str;
				str = init_string("");

				POOL_CONNECTION_POOL_SLOT *system_db = pool_system_db_connection();

				examInTransactionStmt(node,backend,message,query_context->original_query);

				message->status = OneNode_do_command(frontend,
													system_db->con,
													message->rewrite_query,
													backend->info->database,
													true,
													true,
													0);

				free_string(str);
			}
			else
			{
				/* The distribution of the INSERT sentence. */
				examInsertStmt(node,backend,message);

				if(message->r_code == 0 )
				{
					/* send the INSERT sentence */
					message->status = OneNode_do_command(frontend,
														CONNECTION(backend,message->r_node),
														message->rewrite_query,
															backend->info->database,
															true,
															false,
															0);
				}
				else if (message->r_code == INSERT_SQL_RESTRICTION)
				{
					/* Restriction case of INSERT sentence */
					pool_send_error_message(frontend, MAJOR(backend), "XX000",
											"pgpool2 sql restriction",
											message->rewrite_query, "", __FILE__,
											__LINE__);

					if(TSTATE(backend, MASTER_NODE_ID) == 'T')
					{
						/* In Transaction, send the invalid message to backend to abort this transaction */
						pool_debug("rewrite_query_stmt(insert): Inside transaction. Abort transaction");
							message->status = pool_parallel_exec(frontend,backend, "POOL_RESET_TSTATE",node,false, query_context);
					}
					else
					{
						/* return "ready for query" to frontend */
						pool_send_readyforquery(frontend);
						message->status=POOL_CONTINUE;
					}
				}
				else
				{
					message->type = node->type;
					message->status = POOL_CONTINUE;
				}
			}
			break;
#if 0
		case T_UpdateStmt:
			/* Improve UpdateStmt for complex query */
			break;
#endif

		case T_TransactionStmt:
		{
			if (!query_context->is_reflected)
			{
				message->type = node->type;
				message->status = POOL_CONTINUE;

				String *str;
				str = init_string("");

				static ConInfoTodblink dblink;
				/* initialize dblink info */
				initdblink(&dblink,backend);

				TransactionStmt *stmt = (TransactionStmt *)node;

				POOL_CONNECTION_POOL_SLOT *system_db = pool_system_db_connection();

				if( (stmt->kind == TRANS_STMT_BEGIN || stmt->kind == TRANS_STMT_START) && pool_get_session_context()->in_transaction == false )
				{
					pool_get_session_context()->in_transaction = true;

					writeTransactionQuery(str, &dblink, true);
					message->status = OneNode_do_command(frontend,
														system_db->con,
														str->data,
														backend->info->database,
														false,
														false,
														0);
					if (message->status != POOL_CONTINUE)
					{
						return message;
					}
				}

				if (pool_get_session_context()->in_transaction == true)
				{
					examInTransactionStmt(node,backend,message,query_context->original_query);

					message->status = OneNode_do_command(frontend,
														system_db->con,
														message->rewrite_query,
														backend->info->database,
														true,
														true,
														0);
					if (message->status != POOL_CONTINUE)
					{
						return message;
					}
				}
				else
				{
					message->type = T_DiscardStmt;
				}

				if( (stmt->kind == TRANS_STMT_COMMIT || stmt->kind == TRANS_STMT_ROLLBACK) && pool_get_session_context()->in_transaction == true )
				{
					pool_get_session_context()->in_transaction = false;

					writeTransactionQuery(str, &dblink, false);
					message->status = OneNode_do_command(frontend,
														system_db->con,
														str->data,
														backend->info->database,
														false,
														false,
														0);

					pool_session_remove_all_cursors();
					pool_session_remove_all_cursor_info();

					if (message->status != POOL_CONTINUE)
					{
						return message;
					}
				}

				free_string(str);
			}
			else
			{
				message->type = node->type;
				message->status = POOL_CONTINUE;
			}
		}
		break;

		case T_FetchStmt:
			if (pool_get_session_context()->in_transaction)
			{
				FetchStmt *stmt = (FetchStmt *)node;

				POOL_CONNECTION_POOL_SLOT *system_db = pool_system_db_connection();

				CursorsInfo* curInfo = pool_session_get_cursor_info(stmt->portalname);

				if (curInfo == NULL || curInfo->table_type)
				{
					if (stmt->ismove)
					{
						examInTransactionStmt(node,backend,message,query_context->original_query);
					}
					else
					{
						examReplicationFetchStmt(node,backend,message,query_context->original_query);
					}

					message->status = OneNode_do_command(frontend,
														system_db->con,
														message->rewrite_query,
														backend->info->database,
														true,
														stmt->ismove,
														0);
				}
				else
				{
					int nodes_count = 0;
					List *node_ids = NULL;
					List *final_counts = NULL;
					bool ismove_real = stmt->ismove;

					int i = 0;
					for (i=0;i<MAX_CONNECTION_SLOTS;i++)
					{
						/* port number == 0 indicates that this server is out of use */
						if (BACKEND_INFO(i).backend_port != 0)
						{
							++nodes_count;
							node_ids = lappend_int(node_ids, i);
							final_counts = lappend(final_counts, (void *)(long) 0);
							pool_debug("Node_id: %d", i);
						}
					}

#define EXECUTE_DISTRIBUTED_FETCH( is_move, need_node_id, node_counts, offset, limit, send_to_frontend, fix_response, result ) \
	stmt->ismove = is_move; \
	examDistributedFetchStmt(node, backend, message, query_context->original_query, need_node_id, node_ids, node_counts, offset, limit); \
 \
	message->status = OneNode_do_command(frontend, \
										system_db->con, \
										message->rewrite_query, \
										backend->info->database, \
										send_to_frontend, \
										fix_response, \
										(void **)(result)); \
	pfree(message->rewrite_query); \
	message->rewrite_query = NULL; \
	list_free(node_counts); \
	node_counts = NULL;

					long int left_count = stmt->howMany;
					List *node_counts = NULL;
					List *start_node_ids = NULL;

					bool over_fetch = false;

					for (i=0;i<nodes_count;i++)
					{
						node_counts = lappend(node_counts, (void *)(long) /*1*/0);
					}

					EXECUTE_DISTRIBUTED_FETCH( false, true, node_counts, 0, 0, false, false, &start_node_ids );

					// Fast cursor move algorithm
					while (left_count /*> nodes_count*/)
					{
						pool_debug("left_count: %ld, nodes_count: %d", left_count, nodes_count);
						long int move_count = left_count == FETCH_ALL ? FETCH_ALL : left_count / (long)nodes_count /*- 1*/;
						if (move_count == 0) move_count = 1;
						pool_debug("move_count: %ld", move_count);

						List *real_move_counts = NULL;

						for (i=0;i<nodes_count;i++)
						{
							node_counts = lappend(node_counts, (void *)(long) /*1*/0);
						}

						List *start_fetch_node_ids = NULL;

						EXECUTE_DISTRIBUTED_FETCH( false, true, node_counts, 0, 0, false, false, &start_fetch_node_ids );

						for (i=0;i<nodes_count;i++)
						{
							node_counts = lappend(node_counts, (void *)move_count);
						}

						String *response = 0;

						EXECUTE_DISTRIBUTED_FETCH( true, true, node_counts, 0, 0, false, true, &response );

						// Count real move counts
						ListCell *lc1 = NULL;
						foreach(lc1, node_ids)
						{
							bool is_found = false;
							char* p_start = strchr(response->data, ' ');
							while ((p_start = strchr(p_start, ',')) != NULL)
							{
								++p_start;
								int ex_node_id = atoi(p_start);
								if (ex_node_id == lfirst_int(lc1))
								{
									char* p_count = strchr(p_start, '-');
									if (p_count)
									{
										++p_count;
										long count = atol(p_count);

										real_move_counts = lappend(real_move_counts, (void *)count);
										is_found = true;
										break;
									}
								}
							}
							if (!is_found)
							{
								real_move_counts = lappend(real_move_counts, (void *)(long) 0);
							}
						}
						free_string(response);

						List* back_counts = NULL;

						for (i=0;i<nodes_count;i++)
						{
							node_counts = lappend(node_counts, (void *)(long) /*1*/0);
						}

						List *fetch_node_ids = NULL;

						EXECUTE_DISTRIBUTED_FETCH( false, true, node_counts, 0, 0, false, false, &fetch_node_ids );

						ListCell *lc_real_move_count = list_head(real_move_counts);
						lc1 = NULL;
						foreach(lc1, node_ids)
						{
							bool is_found = false;
							ListCell* lc_fetch = NULL;
							foreach(lc_fetch, fetch_node_ids)
							{
								if (lfirst_int(lc1) == lfirst_int(lc_fetch))
								{
									//lfirst(lc_real_move_count) = (void *)((long)lfirst(lc_real_move_count)/* + 1*/);
									is_found = true;
								}
							}
							if (!is_found)
							{
								if ((long)lfirst(lc_real_move_count))
								{
									back_counts = lappend(back_counts, (void *)( (long)lfirst(lc_real_move_count) + 1));
								}
								else
								{
									bool is_found2 = false;
									ListCell* lc_fetch2 = NULL;
									foreach(lc_fetch2, start_fetch_node_ids)
									{
										if (lfirst_int(lc1) == lfirst_int(lc_fetch2))
										{
											is_found2 = true;
										}
									}
									if (is_found2)
									{
										back_counts = lappend(back_counts, (void *)( (long)lfirst(lc_real_move_count) + 1));
									}
									else
									{
										back_counts = lappend(back_counts, (void *)( 0 ));
									}
								}
							}
							else
							{
								back_counts = lappend(back_counts, (void *)(long) lfirst(lc_real_move_count));
							}
							lc_real_move_count = lnext(lc_real_move_count);
						}

						if (list_length(fetch_node_ids))
						{
							bool condition = stmt->direction == (FETCH_FORWARD && stmt->howMany >= 0) || (stmt->direction == FETCH_BACKWARD && stmt->howMany < 0);
							int best_node_id = condition ? lfirst_int(list_head(fetch_node_ids)) : lfirst_int(list_tail(fetch_node_ids));
							pool_debug("best_node_id: %d", best_node_id);

							ListCell *lc = NULL; ListCell *lc_final_count = list_head(final_counts); lc_real_move_count = list_head(real_move_counts);
							ListCell *lc_back = list_head(back_counts);
							foreach(lc, node_ids)
							{
								if (lfirst_int(lc) == best_node_id)
								{
									node_counts = lappend(node_counts, (void *)(long) 0);
									lfirst(lc_final_count) = (void *)((long)lfirst(lc_final_count) + (long)lfirst(lc_real_move_count));
									pool_debug("final_count for node_id %d is %ld", best_node_id, (long)lfirst(lc_final_count));

									left_count -= (long)lfirst(lc_real_move_count);
								}
								else
								{
									node_counts = lappend(node_counts, (void *)(long) (-((long)lfirst(lc_back))));
								}

								lc_final_count = lnext(lc_final_count);
								lc_real_move_count = lnext(lc_real_move_count);
								lc_back = lnext(lc_back);
							}
						}
						else
						{
							ListCell *lc = NULL; ListCell *lc_final_count = list_head(final_counts); lc_real_move_count = list_head(real_move_counts);
							ListCell *lc_back = list_head(back_counts);
							foreach(lc, node_ids)
							{
								lfirst(lc_final_count) = (void *)((long)lfirst(lc_final_count) + (long)lfirst(lc_real_move_count) /*+ 1!!!*/);
								if ((long)lfirst(lc_real_move_count) != (long)lfirst(lc_back))
								{
									node_counts = lappend(node_counts, (void *)(long) -1);
								}
								else
								{
									node_counts = lappend(node_counts, (void *)(long) 0);
								}

								lc_final_count = lnext(lc_final_count);
								lc_real_move_count = lnext(lc_real_move_count);
								lc_back = lnext(lc_back);
							}

							left_count = 0;
							over_fetch = true;
						}
						list_free(fetch_node_ids);
						fetch_node_ids = NULL;

						EXECUTE_DISTRIBUTED_FETCH( true, false, node_counts, 0, 0, false, false, 0 );

						list_free(real_move_counts);
						real_move_counts = NULL;

						ListCell* lc_final_count = NULL;
						foreach(lc_final_count, final_counts)
						{
							pool_debug("Final counts: %ld", (long)lfirst(lc_final_count));
						}
					}

					{
						ListCell* lc = NULL;
						foreach(lc, final_counts)
						{
							long count_back = -((long)lfirst(lc));
							node_counts = lappend(node_counts, (void *)count_back);
							pool_debug("Final counts: %ld", -count_back);
						}
					}

					// Ok, we know now move counts in each node. Go back.
					EXECUTE_DISTRIBUTED_FETCH( true, false, node_counts, 0, 0, false, false, 0 );

					if (over_fetch)
					{
						ListCell* lc_final;
						foreach(lc_final, final_counts)
						{
							lfirst(lc_final) = (void *)((long)lfirst(lc_final) + (long)1);
						}
					}

					int offset = 0, limit = 0;
					if (!ismove_real)
					{
						long sum = 0; int extra = 0;
						ListCell* lc_final; ListCell *lc_ids = list_head(node_ids);
						foreach(lc_final, final_counts)
						{
							sum += (long)lfirst(lc_final);
							if ((long)lfirst(lc_final) == (long)0)
							{
								ListCell* lc_fetch2 = NULL;
								foreach(lc_fetch2, start_node_ids)
								{
									if (lfirst_int(lc_fetch2) == lfirst_int(lc_ids))
									{
										++extra;
										break;
									}
								}
							}

							lc_ids = lnext(lc_ids);
						}

						if (stmt->direction == FETCH_FORWARD)
						{
							limit = sum == 0 ? 1 : sum;
							offset = sum == 0 ? extra - 1 : extra;
							if (offset < 0) offset = 0;
						}
						else if (stmt->direction == FETCH_BACKWARD)
						{
							limit = sum == 0 ? 1 : sum;
						}
					}

					// Finally, we can execute query
					EXECUTE_DISTRIBUTED_FETCH( ismove_real, false, final_counts, offset, limit, true, stmt->ismove, 0 );

#undef EXECUTE_DISTRIBUTED_FETCH
				}
			}
			else
			{
				FetchStmt *stmt = (FetchStmt *)node;
				long int howMany_real = stmt->howMany;

				ListCell* lc = NULL;
				foreach(lc, query_context->move_counts)
				{
					stmt->howMany = (long) lfirst(lc);

					char * new_query = nodeToString(node);
					query_context->move_queries = lappend(query_context->move_queries, (void *)new_query);
				}

				stmt->howMany = howMany_real;

				message->type = node->type;
				message->status = POOL_CONTINUE;
			}
			break;

			case T_DiscardStmt:
			    if (pool_get_session_context()->in_transaction)
			    {
			    	String *str;
			    	str = init_string("");

			    	static ConInfoTodblink dblink;
			    	/* initialize dblink info */
			    	initdblink(&dblink,backend);

			    	POOL_CONNECTION_POOL_SLOT *system_db = pool_system_db_connection();

			    	examInTransactionStmt(node,backend,message,"ROLLBACK;");
			    	OneNode_do_command(frontend,
										system_db->con,
										message->rewrite_query,
										backend->info->database,
										false,
										false,
										0);

			    	examInTransactionStmt(node,backend,message,query_context->original_query);
			    	message->status = OneNode_do_command(frontend,
														system_db->con,
														message->rewrite_query,
														backend->info->database,
														true,
														true,
														0);

			    	pool_get_session_context()->in_transaction = false;

			    	writeTransactionQuery(str, &dblink, false);
			    	OneNode_do_command(frontend,
										system_db->con,
										str->data,
										backend->info->database,
										false,
										false,
										0);

			    	pool_session_remove_all_cursors();
			    	pool_session_remove_all_cursor_info();

			    	free_string(str);
			    }

		    	message->type = node->type;
		        message->status = POOL_CONTINUE;

			    break;

		default:
			if (pool_get_session_context()->in_transaction)
			{
				String *str;
				str = init_string("");

				POOL_CONNECTION_POOL_SLOT *system_db = pool_system_db_connection();

				examInTransactionStmt(node,backend,message,query_context->original_query);

				message->status = OneNode_do_command(frontend,
													system_db->con,
													message->rewrite_query,
													backend->info->database,
													true,
													true,
													0);

				free_string(str);
			}
			else
			{
			message->type = node->type;
			message->status = POOL_CONTINUE;
			}
			break;
	}

	pool_debug("pool_rewrite_stmt: query rule %d",node->type);

	return message;
}

#define POOL_PARALLEL "pool_parallel"
#define POOL_LOADBALANCE "pool_loadbalance"
#define POOL_NORMAL "pool_transaction"
#define POOL_CURSOR_MOVE "pool_move"
#define POOL_CURSOR_FETCH "pool_fetch"

/*
 * After analyzing query, check the analyze[0]->state.
 * if the analyze[0]->state ==`P`, this query can be executed
 * on parallel engine.
 */
static int direct_parallel_query(RewriteQuery *message)
{
	if(message && message->analyze[0] && message->analyze[0]->state == 'P')
		return 1;
	else
		return 0;
}


/* escape delimiter character */
static char *delimistr(char *str)
{
	char *result;
	int i,j = 0;
	int len = strlen(str);

	result = palloc(len -1);

	for(i = 0; i < len; i++)
	{
		char c = (unsigned char) str[i];
		if((i != 0) && (i != len -1))
		{
			/*if(c=='\'' && (char) str[i+1]=='\'')
				i++;*/
			result[j] = c;
			j++;
		}
	}

	result[j] = '\0';

	return result;
}

/* for debug */
void analyze_debug(RewriteQuery *message)
{
	int analyze_num,i;
	analyze_num = message->analyze_num;

	for(i = 0; i< analyze_num; i++)
	{
		AnalyzeSelect *analyze = message->analyze[i];
		pool_debug("analyze_debug :select no(%d), last select(%d), last_part(%d), state(%c)",
             analyze->now_select,analyze->last_select,analyze->call_part,analyze->state);
	}
}

/*
 * This function checks the KEYWORD(POOL_PARALLEL,POOL_LOADBALANCE)
 * if the special function(like pool_parallel() or pool_loadbalance())
 * is used, mark the r_code,is_parallel and is_loadbalance.
 * In othe cases, It is necessary to analyze the Query.
 */
RewriteQuery *is_parallel_query(Node *node, POOL_CONNECTION_POOL *backend, POOL_QUERY_CONTEXT *query_context)
{
	static RewriteQuery message;
	static ConInfoTodblink dblink;

	initMessage(&message); message.strange_nodes_num = 0;

	if (IsA(node, SelectStmt))
	{
		SelectStmt *stmt;
		Node *n;
		int direct_ok;

		stmt = (SelectStmt *) (node);

		/* Check the special function is used in this query*/
		if (!(stmt->distinctClause || stmt->intoClause ||
			stmt->fromClause || stmt->groupClause || stmt->havingClause ||
			stmt->sortClause || stmt->limitOffset || stmt->limitCount ||
			stmt->lockingClause || stmt->larg || stmt->rarg) &&
			(n = lfirst(list_head(stmt->targetList))) && IsA(n, ResTarget))
		{
			ResTarget *target = (ResTarget *) n;

			if (target->val && IsA(target->val, FuncCall))
			{
				FuncCall *func = (FuncCall *) target->val;
				if (list_length(func->funcname) == 1 && func->args)
				{
					Node *func_args = (Node *) lfirst(list_head(func->args));
					message.rewrite_query = delimistr(nodeToString(func_args));

					/* pool_parallel() is used in this query */
					if(strcmp(strVal(lfirst(list_head(func->funcname))),
						   POOL_PARALLEL) == 0)
					{
						message.r_code = SEND_PARALLEL_ENGINE;
						message.is_parallel = true;
						message.is_loadbalance = false;
						pool_debug("can pool_parallel_exec %s",message.rewrite_query);
						return &message;
					}
					else /* pool_loadbalance() is used in this query */
					if(strcmp(strVal(lfirst(list_head(func->funcname))),
						   						POOL_LOADBALANCE) == 0)
					{
						message.r_code = SEND_LOADBALANCE_ENGINE;
						message.is_loadbalance = true;
						message.is_parallel = false;
						pool_debug("can loadbalance_mode %s",message.rewrite_query);
						return &message;
					}
					else
					if(strcmp(strVal(lfirst(list_head(func->funcname))),
							POOL_NORMAL) == 0)
					{
						message.is_reflected = true;
						pool_debug("can normal_mode %s",message.rewrite_query);
						return &message;
					}
					else
					if(strcmp(strVal(lfirst(list_head(func->funcname))),
							POOL_CURSOR_MOVE) == 0)
					{
						message.is_reflected = true;
						message.is_cursor_move = true;

						ListCell* lc = NULL; bool is_id = true; bool first_param = true;
						for_each_cell(lc, lnext(list_head(func->args)))
						{
							Node *params = (Node *) lfirst(lc);
							if( first_param )
							{
								query_context->need_fetch_node_id = atoi(delimistr(nodeToString(params)));
								first_param = false;
								continue;
							}
							if( is_id )
							{
								int node_id = atoi(delimistr(nodeToString(params)));
								pool_debug("node_id: %d", node_id);
								query_context->move_counts_ids = lappend_int(query_context->move_counts_ids, node_id);
							}
							else
							{
								long howMany = atol(delimistr(nodeToString(params)));
								pool_debug("howMany: %ld", howMany);
								query_context->move_counts = lappend(query_context->move_counts, (void *)howMany);
							}
							is_id = !is_id;
						}

						pool_debug("can cursor move %s",message.rewrite_query);
						return &message;
					}
				}
			}
		}

    /* ANALYZE QUERY */
		message.r_code = SELECT_ANALYZE;
		message.is_loadbalance = true;

		initdblink(&dblink,backend);
		nodeToRewriteString(&message,&dblink,node);

		query_context->is_loadbalance = message.is_loadbalance;

		if(message.is_pg_catalog)
		{
			message.is_loadbalance = false;
			message.is_parallel = false;
			pool_debug("is_parallel_query: query is done by loadbalance(pgcatalog)");
			return &message;
		}

		if(message.is_loadbalance)
		{
			message.is_parallel = false;
			if( !pool_get_session_context()->in_transaction )
			{
			pool_debug("is_parallel_query: query is done by loadbalance");
			return &message;
		}
			else
			{
				message.is_loadbalance = false;
			}
		}

		/* Analyzing Query Start */
		analyze_debug(&message);

		/* After the analyzing query,
		 * this query can be executed as parallel exec, is_parallel flag is turned on
		 */
		direct_ok = direct_parallel_query(&message);
		if(direct_ok == 1)
		{
			message.rewrite_query = nodeToString(node);
			message.is_parallel = true;
			message.is_loadbalance = false;
			pool_debug("can pool_parallel_exec %s",message.rewrite_query);
			return &message;
		}
	}
	else if (IsA(node, CopyStmt))
	{
		/* For Copy Statement, check the table name, mark the is_parallel flag. */
		CopyStmt *stmt = (CopyStmt *)node;

		if (stmt->is_from == FALSE && stmt->filename == NULL)
		{
			RangeVar *relation = (RangeVar *)stmt->relation;

			/* check on distribution table or replicate table */

			if(pool_get_dist_def_info (MASTER_CONNECTION(backend)->sp->database, relation->schemaname, relation->relname))
			{
				message.rewrite_query = nodeToString(stmt);
				message.is_parallel = true;
				message.is_loadbalance = false;
				message.r_code = SEND_PARALLEL_ENGINE;
			}
		}
	}
	else if (IsA(node, DeclareCursorStmt))
	{
		DeclareCursorStmt *stmt = (DeclareCursorStmt *) (node);

		/* ANALYZE QUERY */
		message.r_code = SELECT_ANALYZE;
		message.is_loadbalance = true;

		initdblink(&dblink,backend);
		nodeToRewriteString(&message,&dblink,node);

		if(message.is_pg_catalog)
		{
			message.is_loadbalance = false;
			message.is_parallel = false;
			pool_debug("is_parallel_query: query is done by loadbalance(pgcatalog)");
			return &message;
		}

		if(message.is_loadbalance)
		{
			message.is_parallel = false;
			if( !pool_get_session_context()->in_transaction )
			{
				message.rewrite_query = nodeToString(stmt);
				message.r_code = SEND_LOADBALANCE_ENGINE;
				pool_debug("is_parallel_query: query is done by loadbalance");
				query_context->replication_cursor = true;
				query_context->loadbalance_cursor = true;
				strncpy(query_context->cursor_name, stmt->portalname, 64);
				return &message;
			}
			else
			{
				String *str;
				str = init_string("");

				message.r_code = SELECT_DEFAULT;
				message.special_info = true;
				extractRepCursorInfo(&message, &dblink, node, str);
				pool_session_add_cursor_info(stmt->portalname, str->data, true);

				message.is_loadbalance = false;
				free_string(str);
			}
		}
		else
		{
			if( !pool_get_session_context()->in_transaction )
			{
				query_context->replication_cursor = false;
				strncpy(query_context->cursor_name, stmt->portalname, 64);
			}
			else
			{
				String *str;
				str = init_string("");

				message.r_code = SELECT_DEFAULT;
				message.special_info = true;
				extractDistCursorInfo(&message, &dblink, node, str);
				pool_session_add_cursor_info(stmt->portalname, str->data, false);

				free_string(str);
			}
		}

		/* Analyzing Query Start */
		analyze_debug(&message);
	}
	else if (IsA(node, ClosePortalStmt))
	{
		ClosePortalStmt *stmt = (ClosePortalStmt *) (node);

		if (!pool_get_session_context()->in_transaction)
		{
			if( stmt->portalname )
			{
				int res = pool_session_find_cursor( stmt->portalname );
				if (res == 1)
				{
					message.is_loadbalance = true;
					message.is_parallel = false;
					message.rewrite_query = nodeToString(stmt);
					message.r_code = SEND_LOADBALANCE_ENGINE;
					query_context->loadbalance_cursor = true;
					pool_debug("is_parallel_query: query is done by loadbalance");
					pool_session_remove_cursor(stmt->portalname, true);
					return &message;
				}
				else if (res == -1)
				{
					pool_session_remove_cursor(stmt->portalname, false);
				}
			}
			else
			{

			}
		}
		else
		{
			pool_session_remove_cursor_info(stmt->portalname);
		}
	}
	else if (IsA(node, FetchStmt))
	{
		FetchStmt *stmt = (FetchStmt *) (node);

		if (!pool_get_session_context()->in_transaction)
		{
			if (stmt->ismove && query_context->need_fetch_node_id)
			{
				query_context->need_fetch_node_id = false;
				query_context->need_merged_cmd_response = true;
			}
			int res = pool_session_find_cursor( stmt->portalname );
			if (res == 1)
			{
				message.is_loadbalance = true;
				message.is_parallel = false;
				message.rewrite_query = nodeToString(stmt);
				message.r_code = SEND_LOADBALANCE_ENGINE;
				query_context->loadbalance_cursor = true;
				pool_debug("is_parallel_query: query is done by loadbalance");
				return &message;
			}
			else if (res == -1)
			{

			}
		}
		else
		{

		}
	}

	return &message;
}

POOL_STATUS pool_do_parallel_query(POOL_CONNECTION *frontend,
								   POOL_CONNECTION_POOL *backend,
								   POOL_QUERY_CONTEXT *query_context,
								   Node *node, bool *parallel, char **string, int *len)
{
	/* The Query is analyzed first in a parallel mode(in_parallel_query),
	 * and, next, the Query is rewritten(rewrite_query_stmt).
	 */

	/* analyze the query */
	RewriteQuery *r_query = is_parallel_query(node,backend,query_context);

	if(r_query->is_reflected && !query_context->is_reflected)
	{
		*string = pstrdup(r_query->rewrite_query);
		*len = strlen(*string)+1;

		query_context->is_reflected = true;

		pool_debug("New statement2: %s", *string);

		return POOL_CONTINUE;
	}
	else if(r_query->is_loadbalance && !(pool_get_session_context()->in_transaction))
	{
        /* Usual processing of pgpool is done by using the rewritten Query
         * if judged a possible load-balancing as a result of analyzing
         * the Query.
         * Of course, the load is distributed only for load_balance_mode=true.
         */
		if(r_query->r_code ==  SEND_LOADBALANCE_ENGINE)
		{
			/* use rewritten query */
			*string = r_query->rewrite_query;
			/* change query length */
			*len = strlen(*string)+1;
			query_context->original_query = *string;
			query_context->original_length = *len;
		}
		pool_debug("pool_do_parallel_query: load balancing query: %s",*string);
	}
	else if (r_query->is_parallel && !(pool_get_session_context()->in_transaction))
	{
		/*
		 * For the Query that the parallel processing is possible.
		 * Call parallel exe engine and return status to the upper layer.
		 */
		POOL_STATUS stats = pool_parallel_exec(frontend,backend,r_query->rewrite_query, node,true, query_context);
		pool_unset_query_in_progress();
		return stats;
	}
	else if(!r_query->is_pg_catalog)
	{
		/* rewrite query and execute */
		r_query = rewrite_query_stmt(node,frontend,backend,r_query,query_context);
		if(pool_get_session_context()->in_transaction)
		{
			pool_unset_query_in_progress();
			pool_set_skip_reading_from_backends();
			return r_query->status;
		}
		else if(r_query->type == T_InsertStmt)
		{
			if(r_query->r_code != INSERT_DIST_NO_RULE)
			{
				pool_unset_query_in_progress();
				pool_set_skip_reading_from_backends();
				return r_query->status;
			}
		}
		else if(r_query->type == T_SelectStmt)
		{
			pool_unset_query_in_progress();
			pool_set_skip_reading_from_backends();
			return r_query->status;
		}
		else if(r_query->type == T_TransactionStmt && !query_context->is_reflected)
		{
			pool_unset_query_in_progress();
			pool_set_skip_reading_from_backends();
			return r_query->status;
		}
	}

	*parallel = false;
	return POOL_CONTINUE;
}
