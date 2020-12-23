%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0271+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 11.07s
% Output     : CNFRefutation 11.07s
% Verified   : 
% Statistics : Number of formulae       :   44 (  79 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 187 expanded)
%              Number of equality atoms :   63 ( 112 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f368,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f367])).

fof(f537,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f368])).

fof(f682,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f537])).

fof(f683,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK35,sK36)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) )
      & ( r2_hidden(sK35,sK36)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ) ) ),
    introduced(choice_axiom,[])).

fof(f684,plain,
    ( ( ~ r2_hidden(sK35,sK36)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) )
    & ( r2_hidden(sK35,sK36)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f682,f683])).

fof(f1190,plain,
    ( r2_hidden(sK35,sK36)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f684])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f692,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1526,plain,
    ( r2_hidden(sK35,sK36)
    | o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(definition_unfolding,[],[f1190,f692])).

fof(f303,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f655,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f303])).

fof(f1087,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f655])).

fof(f1451,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1087,f692])).

fof(f1086,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f655])).

fof(f1452,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f1086,f692])).

fof(f340,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f672,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f673,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f672])).

fof(f1146,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f673])).

fof(f1600,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1146])).

fof(f369,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f538,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f369])).

fof(f1192,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f538])).

fof(f1191,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f684])).

fof(f1525,plain,
    ( ~ r2_hidden(sK35,sK36)
    | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(definition_unfolding,[],[f1191,f692])).

cnf(c_494,negated_conjecture,
    ( r2_hidden(sK35,sK36)
    | o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1526])).

cnf(c_14651,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36)
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_389,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1451])).

cnf(c_14699,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_22015,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_14651,c_14699])).

cnf(c_390,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1452])).

cnf(c_14698,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_23482,plain,
    ( r2_hidden(sK35,sK36) = iProver_top ),
    inference(superposition,[status(thm)],[c_22015,c_14698])).

cnf(c_8821,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_18476,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(instantiation,[status(thm)],[c_8821])).

cnf(c_18477,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18476])).

cnf(c_447,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1600])).

cnf(c_604,plain,
    ( r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_495,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1192])).

cnf(c_502,plain,
    ( ~ r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_493,negated_conjecture,
    ( ~ r2_hidden(sK35,sK36)
    | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1525])).

cnf(c_499,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36)
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23482,c_22015,c_18477,c_604,c_502,c_499])).

%------------------------------------------------------------------------------
