%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0272+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 14.70s
% Output     : CNFRefutation 14.70s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 (  99 expanded)
%              Number of equality atoms :   57 (  71 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f683,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f367])).

fof(f1192,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f683])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f693,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1528,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1192,f693])).

fof(f366,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f682,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f366])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f682])).

fof(f340,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f673,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f674,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f673])).

fof(f1147,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f674])).

fof(f1604,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1147])).

fof(f370,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f539,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f370])).

fof(f1195,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f539])).

fof(f368,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f369,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f368])).

fof(f538,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f369])).

fof(f684,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ) ),
    introduced(choice_axiom,[])).

fof(f685,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f538,f684])).

fof(f1194,plain,(
    k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f685])).

fof(f1193,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f685])).

fof(f1530,plain,(
    o_0_0_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(definition_unfolding,[],[f1193,f693])).

cnf(c_493,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1528])).

cnf(c_21201,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_8783,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_18177,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(instantiation,[status(thm)],[c_8783])).

cnf(c_18178,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK35),sK36)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18177])).

cnf(c_491,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1190])).

cnf(c_17696,plain,
    ( r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_447,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1604])).

cnf(c_610,plain,
    ( r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_497,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1195])).

cnf(c_502,plain,
    ( ~ r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_495,negated_conjecture,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1194])).

cnf(c_496,negated_conjecture,
    ( o_0_0_xboole_0 != k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1530])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21201,c_18178,c_17696,c_610,c_502,c_495,c_496])).

%------------------------------------------------------------------------------
