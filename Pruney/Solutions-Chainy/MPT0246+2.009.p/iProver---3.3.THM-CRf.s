%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:03 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 200 expanded)
%              Number of clauses        :   47 (  64 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  235 ( 583 expanded)
%              Number of equality atoms :  101 ( 258 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK5 = X2
          | ~ r2_hidden(X2,sK4) )
      & k1_xboole_0 != sK4
      & k1_tarski(sK5) != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X2] :
        ( sK5 = X2
        | ~ r2_hidden(X2,sK4) )
    & k1_xboole_0 != sK4
    & k1_tarski(sK5) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f36])).

fof(f63,plain,(
    ! [X2] :
      ( sK5 = X2
      | ~ r2_hidden(X2,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f30])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f62,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    k1_tarski(sK5) != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f69,plain,(
    k2_enumset1(sK5,sK5,sK5,sK5) != sK4 ),
    inference(definition_unfolding,[],[f61,f65])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1926,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_4047,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_4049,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_4047])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_652,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_666,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | sK5 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_649,plain,
    ( sK5 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1357,plain,
    ( sK0(sK4,X0) = sK5
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_666,c_649])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_655,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2151,plain,
    ( sK0(sK4,X0) = sK5
    | sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_655])).

cnf(c_3098,plain,
    ( k2_enumset1(X0,X0,X0,X1) = sK4
    | sK0(sK4,k2_enumset1(X0,X0,X0,X1)) = sK5
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_2151])).

cnf(c_3103,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = sK4
    | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3098])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1751,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_656,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1351,plain,
    ( sK3(sK4) = sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_656,c_649])).

cnf(c_1467,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_656])).

cnf(c_1468,plain,
    ( r2_hidden(sK5,sK4)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1467])).

cnf(c_351,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_767,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1314,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_654,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_650,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1252,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_650])).

cnf(c_1253,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1252])).

cnf(c_1255,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_890,plain,
    ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_tarski(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_886,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_818,plain,
    ( ~ r2_hidden(sK5,sK4)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_708,plain,
    ( ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4)
    | ~ r1_tarski(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_690,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_354,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_358,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK5,sK5,sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_42,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK4 ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4049,c_3103,c_1751,c_1468,c_1467,c_1314,c_1255,c_890,c_886,c_818,c_708,c_690,c_358,c_42,c_38,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.03  
% 3.84/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.03  
% 3.84/1.03  ------  iProver source info
% 3.84/1.03  
% 3.84/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.03  git: non_committed_changes: false
% 3.84/1.03  git: last_make_outside_of_git: false
% 3.84/1.03  
% 3.84/1.03  ------ 
% 3.84/1.03  
% 3.84/1.03  ------ Input Options
% 3.84/1.03  
% 3.84/1.03  --out_options                           all
% 3.84/1.03  --tptp_safe_out                         true
% 3.84/1.03  --problem_path                          ""
% 3.84/1.03  --include_path                          ""
% 3.84/1.03  --clausifier                            res/vclausify_rel
% 3.84/1.03  --clausifier_options                    ""
% 3.84/1.03  --stdin                                 false
% 3.84/1.03  --stats_out                             all
% 3.84/1.03  
% 3.84/1.03  ------ General Options
% 3.84/1.03  
% 3.84/1.03  --fof                                   false
% 3.84/1.03  --time_out_real                         305.
% 3.84/1.03  --time_out_virtual                      -1.
% 3.84/1.03  --symbol_type_check                     false
% 3.84/1.03  --clausify_out                          false
% 3.84/1.03  --sig_cnt_out                           false
% 3.84/1.03  --trig_cnt_out                          false
% 3.84/1.03  --trig_cnt_out_tolerance                1.
% 3.84/1.03  --trig_cnt_out_sk_spl                   false
% 3.84/1.03  --abstr_cl_out                          false
% 3.84/1.03  
% 3.84/1.03  ------ Global Options
% 3.84/1.03  
% 3.84/1.03  --schedule                              default
% 3.84/1.03  --add_important_lit                     false
% 3.84/1.03  --prop_solver_per_cl                    1000
% 3.84/1.03  --min_unsat_core                        false
% 3.84/1.03  --soft_assumptions                      false
% 3.84/1.03  --soft_lemma_size                       3
% 3.84/1.03  --prop_impl_unit_size                   0
% 3.84/1.03  --prop_impl_unit                        []
% 3.84/1.03  --share_sel_clauses                     true
% 3.84/1.03  --reset_solvers                         false
% 3.84/1.03  --bc_imp_inh                            [conj_cone]
% 3.84/1.03  --conj_cone_tolerance                   3.
% 3.84/1.03  --extra_neg_conj                        none
% 3.84/1.03  --large_theory_mode                     true
% 3.84/1.03  --prolific_symb_bound                   200
% 3.84/1.03  --lt_threshold                          2000
% 3.84/1.03  --clause_weak_htbl                      true
% 3.84/1.03  --gc_record_bc_elim                     false
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing Options
% 3.84/1.03  
% 3.84/1.03  --preprocessing_flag                    true
% 3.84/1.03  --time_out_prep_mult                    0.1
% 3.84/1.03  --splitting_mode                        input
% 3.84/1.03  --splitting_grd                         true
% 3.84/1.03  --splitting_cvd                         false
% 3.84/1.03  --splitting_cvd_svl                     false
% 3.84/1.03  --splitting_nvd                         32
% 3.84/1.03  --sub_typing                            true
% 3.84/1.03  --prep_gs_sim                           true
% 3.84/1.03  --prep_unflatten                        true
% 3.84/1.03  --prep_res_sim                          true
% 3.84/1.03  --prep_upred                            true
% 3.84/1.03  --prep_sem_filter                       exhaustive
% 3.84/1.03  --prep_sem_filter_out                   false
% 3.84/1.03  --pred_elim                             true
% 3.84/1.03  --res_sim_input                         true
% 3.84/1.03  --eq_ax_congr_red                       true
% 3.84/1.03  --pure_diseq_elim                       true
% 3.84/1.03  --brand_transform                       false
% 3.84/1.03  --non_eq_to_eq                          false
% 3.84/1.03  --prep_def_merge                        true
% 3.84/1.03  --prep_def_merge_prop_impl              false
% 3.84/1.03  --prep_def_merge_mbd                    true
% 3.84/1.03  --prep_def_merge_tr_red                 false
% 3.84/1.03  --prep_def_merge_tr_cl                  false
% 3.84/1.03  --smt_preprocessing                     true
% 3.84/1.03  --smt_ac_axioms                         fast
% 3.84/1.03  --preprocessed_out                      false
% 3.84/1.03  --preprocessed_stats                    false
% 3.84/1.03  
% 3.84/1.03  ------ Abstraction refinement Options
% 3.84/1.03  
% 3.84/1.03  --abstr_ref                             []
% 3.84/1.03  --abstr_ref_prep                        false
% 3.84/1.03  --abstr_ref_until_sat                   false
% 3.84/1.03  --abstr_ref_sig_restrict                funpre
% 3.84/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.03  --abstr_ref_under                       []
% 3.84/1.03  
% 3.84/1.03  ------ SAT Options
% 3.84/1.03  
% 3.84/1.03  --sat_mode                              false
% 3.84/1.03  --sat_fm_restart_options                ""
% 3.84/1.03  --sat_gr_def                            false
% 3.84/1.03  --sat_epr_types                         true
% 3.84/1.03  --sat_non_cyclic_types                  false
% 3.84/1.03  --sat_finite_models                     false
% 3.84/1.03  --sat_fm_lemmas                         false
% 3.84/1.03  --sat_fm_prep                           false
% 3.84/1.03  --sat_fm_uc_incr                        true
% 3.84/1.03  --sat_out_model                         small
% 3.84/1.03  --sat_out_clauses                       false
% 3.84/1.03  
% 3.84/1.03  ------ QBF Options
% 3.84/1.03  
% 3.84/1.03  --qbf_mode                              false
% 3.84/1.03  --qbf_elim_univ                         false
% 3.84/1.03  --qbf_dom_inst                          none
% 3.84/1.03  --qbf_dom_pre_inst                      false
% 3.84/1.03  --qbf_sk_in                             false
% 3.84/1.03  --qbf_pred_elim                         true
% 3.84/1.03  --qbf_split                             512
% 3.84/1.03  
% 3.84/1.03  ------ BMC1 Options
% 3.84/1.03  
% 3.84/1.03  --bmc1_incremental                      false
% 3.84/1.03  --bmc1_axioms                           reachable_all
% 3.84/1.03  --bmc1_min_bound                        0
% 3.84/1.03  --bmc1_max_bound                        -1
% 3.84/1.03  --bmc1_max_bound_default                -1
% 3.84/1.03  --bmc1_symbol_reachability              true
% 3.84/1.03  --bmc1_property_lemmas                  false
% 3.84/1.03  --bmc1_k_induction                      false
% 3.84/1.03  --bmc1_non_equiv_states                 false
% 3.84/1.03  --bmc1_deadlock                         false
% 3.84/1.03  --bmc1_ucm                              false
% 3.84/1.03  --bmc1_add_unsat_core                   none
% 3.84/1.03  --bmc1_unsat_core_children              false
% 3.84/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.03  --bmc1_out_stat                         full
% 3.84/1.03  --bmc1_ground_init                      false
% 3.84/1.03  --bmc1_pre_inst_next_state              false
% 3.84/1.03  --bmc1_pre_inst_state                   false
% 3.84/1.03  --bmc1_pre_inst_reach_state             false
% 3.84/1.03  --bmc1_out_unsat_core                   false
% 3.84/1.03  --bmc1_aig_witness_out                  false
% 3.84/1.03  --bmc1_verbose                          false
% 3.84/1.03  --bmc1_dump_clauses_tptp                false
% 3.84/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.03  --bmc1_dump_file                        -
% 3.84/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.03  --bmc1_ucm_extend_mode                  1
% 3.84/1.03  --bmc1_ucm_init_mode                    2
% 3.84/1.03  --bmc1_ucm_cone_mode                    none
% 3.84/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.03  --bmc1_ucm_relax_model                  4
% 3.84/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.03  --bmc1_ucm_layered_model                none
% 3.84/1.03  --bmc1_ucm_max_lemma_size               10
% 3.84/1.03  
% 3.84/1.03  ------ AIG Options
% 3.84/1.03  
% 3.84/1.03  --aig_mode                              false
% 3.84/1.03  
% 3.84/1.03  ------ Instantiation Options
% 3.84/1.03  
% 3.84/1.03  --instantiation_flag                    true
% 3.84/1.03  --inst_sos_flag                         true
% 3.84/1.03  --inst_sos_phase                        true
% 3.84/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel_side                     num_symb
% 3.84/1.03  --inst_solver_per_active                1400
% 3.84/1.03  --inst_solver_calls_frac                1.
% 3.84/1.03  --inst_passive_queue_type               priority_queues
% 3.84/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.03  --inst_passive_queues_freq              [25;2]
% 3.84/1.03  --inst_dismatching                      true
% 3.84/1.03  --inst_eager_unprocessed_to_passive     true
% 3.84/1.03  --inst_prop_sim_given                   true
% 3.84/1.03  --inst_prop_sim_new                     false
% 3.84/1.03  --inst_subs_new                         false
% 3.84/1.03  --inst_eq_res_simp                      false
% 3.84/1.03  --inst_subs_given                       false
% 3.84/1.03  --inst_orphan_elimination               true
% 3.84/1.03  --inst_learning_loop_flag               true
% 3.84/1.03  --inst_learning_start                   3000
% 3.84/1.03  --inst_learning_factor                  2
% 3.84/1.03  --inst_start_prop_sim_after_learn       3
% 3.84/1.03  --inst_sel_renew                        solver
% 3.84/1.03  --inst_lit_activity_flag                true
% 3.84/1.03  --inst_restr_to_given                   false
% 3.84/1.03  --inst_activity_threshold               500
% 3.84/1.03  --inst_out_proof                        true
% 3.84/1.03  
% 3.84/1.03  ------ Resolution Options
% 3.84/1.03  
% 3.84/1.03  --resolution_flag                       true
% 3.84/1.03  --res_lit_sel                           adaptive
% 3.84/1.03  --res_lit_sel_side                      none
% 3.84/1.03  --res_ordering                          kbo
% 3.84/1.03  --res_to_prop_solver                    active
% 3.84/1.03  --res_prop_simpl_new                    false
% 3.84/1.03  --res_prop_simpl_given                  true
% 3.84/1.03  --res_passive_queue_type                priority_queues
% 3.84/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.03  --res_passive_queues_freq               [15;5]
% 3.84/1.03  --res_forward_subs                      full
% 3.84/1.03  --res_backward_subs                     full
% 3.84/1.03  --res_forward_subs_resolution           true
% 3.84/1.03  --res_backward_subs_resolution          true
% 3.84/1.03  --res_orphan_elimination                true
% 3.84/1.03  --res_time_limit                        2.
% 3.84/1.03  --res_out_proof                         true
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Options
% 3.84/1.03  
% 3.84/1.03  --superposition_flag                    true
% 3.84/1.03  --sup_passive_queue_type                priority_queues
% 3.84/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.03  --demod_completeness_check              fast
% 3.84/1.03  --demod_use_ground                      true
% 3.84/1.03  --sup_to_prop_solver                    passive
% 3.84/1.03  --sup_prop_simpl_new                    true
% 3.84/1.03  --sup_prop_simpl_given                  true
% 3.84/1.03  --sup_fun_splitting                     true
% 3.84/1.03  --sup_smt_interval                      50000
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Simplification Setup
% 3.84/1.03  
% 3.84/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_immed_triv                        [TrivRules]
% 3.84/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_bw_main                     []
% 3.84/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_input_bw                          []
% 3.84/1.03  
% 3.84/1.03  ------ Combination Options
% 3.84/1.03  
% 3.84/1.03  --comb_res_mult                         3
% 3.84/1.03  --comb_sup_mult                         2
% 3.84/1.03  --comb_inst_mult                        10
% 3.84/1.03  
% 3.84/1.03  ------ Debug Options
% 3.84/1.03  
% 3.84/1.03  --dbg_backtrace                         false
% 3.84/1.03  --dbg_dump_prop_clauses                 false
% 3.84/1.03  --dbg_dump_prop_clauses_file            -
% 3.84/1.03  --dbg_out_stat                          false
% 3.84/1.03  ------ Parsing...
% 3.84/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.03  ------ Proving...
% 3.84/1.03  ------ Problem Properties 
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  clauses                                 22
% 3.84/1.03  conjectures                             3
% 3.84/1.03  EPR                                     6
% 3.84/1.03  Horn                                    15
% 3.84/1.03  unary                                   5
% 3.84/1.03  binary                                  8
% 3.84/1.03  lits                                    49
% 3.84/1.03  lits eq                                 11
% 3.84/1.03  fd_pure                                 0
% 3.84/1.03  fd_pseudo                               0
% 3.84/1.03  fd_cond                                 2
% 3.84/1.03  fd_pseudo_cond                          6
% 3.84/1.03  AC symbols                              0
% 3.84/1.03  
% 3.84/1.03  ------ Schedule dynamic 5 is on 
% 3.84/1.03  
% 3.84/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  ------ 
% 3.84/1.03  Current options:
% 3.84/1.03  ------ 
% 3.84/1.03  
% 3.84/1.03  ------ Input Options
% 3.84/1.03  
% 3.84/1.03  --out_options                           all
% 3.84/1.03  --tptp_safe_out                         true
% 3.84/1.03  --problem_path                          ""
% 3.84/1.03  --include_path                          ""
% 3.84/1.03  --clausifier                            res/vclausify_rel
% 3.84/1.03  --clausifier_options                    ""
% 3.84/1.03  --stdin                                 false
% 3.84/1.03  --stats_out                             all
% 3.84/1.03  
% 3.84/1.03  ------ General Options
% 3.84/1.03  
% 3.84/1.03  --fof                                   false
% 3.84/1.03  --time_out_real                         305.
% 3.84/1.03  --time_out_virtual                      -1.
% 3.84/1.03  --symbol_type_check                     false
% 3.84/1.03  --clausify_out                          false
% 3.84/1.03  --sig_cnt_out                           false
% 3.84/1.03  --trig_cnt_out                          false
% 3.84/1.03  --trig_cnt_out_tolerance                1.
% 3.84/1.03  --trig_cnt_out_sk_spl                   false
% 3.84/1.03  --abstr_cl_out                          false
% 3.84/1.03  
% 3.84/1.03  ------ Global Options
% 3.84/1.03  
% 3.84/1.03  --schedule                              default
% 3.84/1.03  --add_important_lit                     false
% 3.84/1.03  --prop_solver_per_cl                    1000
% 3.84/1.03  --min_unsat_core                        false
% 3.84/1.03  --soft_assumptions                      false
% 3.84/1.03  --soft_lemma_size                       3
% 3.84/1.03  --prop_impl_unit_size                   0
% 3.84/1.03  --prop_impl_unit                        []
% 3.84/1.03  --share_sel_clauses                     true
% 3.84/1.03  --reset_solvers                         false
% 3.84/1.03  --bc_imp_inh                            [conj_cone]
% 3.84/1.03  --conj_cone_tolerance                   3.
% 3.84/1.03  --extra_neg_conj                        none
% 3.84/1.03  --large_theory_mode                     true
% 3.84/1.03  --prolific_symb_bound                   200
% 3.84/1.03  --lt_threshold                          2000
% 3.84/1.03  --clause_weak_htbl                      true
% 3.84/1.03  --gc_record_bc_elim                     false
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing Options
% 3.84/1.03  
% 3.84/1.03  --preprocessing_flag                    true
% 3.84/1.03  --time_out_prep_mult                    0.1
% 3.84/1.03  --splitting_mode                        input
% 3.84/1.03  --splitting_grd                         true
% 3.84/1.03  --splitting_cvd                         false
% 3.84/1.03  --splitting_cvd_svl                     false
% 3.84/1.03  --splitting_nvd                         32
% 3.84/1.03  --sub_typing                            true
% 3.84/1.03  --prep_gs_sim                           true
% 3.84/1.03  --prep_unflatten                        true
% 3.84/1.03  --prep_res_sim                          true
% 3.84/1.03  --prep_upred                            true
% 3.84/1.03  --prep_sem_filter                       exhaustive
% 3.84/1.03  --prep_sem_filter_out                   false
% 3.84/1.03  --pred_elim                             true
% 3.84/1.03  --res_sim_input                         true
% 3.84/1.03  --eq_ax_congr_red                       true
% 3.84/1.03  --pure_diseq_elim                       true
% 3.84/1.03  --brand_transform                       false
% 3.84/1.03  --non_eq_to_eq                          false
% 3.84/1.03  --prep_def_merge                        true
% 3.84/1.03  --prep_def_merge_prop_impl              false
% 3.84/1.03  --prep_def_merge_mbd                    true
% 3.84/1.03  --prep_def_merge_tr_red                 false
% 3.84/1.03  --prep_def_merge_tr_cl                  false
% 3.84/1.03  --smt_preprocessing                     true
% 3.84/1.03  --smt_ac_axioms                         fast
% 3.84/1.03  --preprocessed_out                      false
% 3.84/1.03  --preprocessed_stats                    false
% 3.84/1.03  
% 3.84/1.03  ------ Abstraction refinement Options
% 3.84/1.03  
% 3.84/1.03  --abstr_ref                             []
% 3.84/1.03  --abstr_ref_prep                        false
% 3.84/1.03  --abstr_ref_until_sat                   false
% 3.84/1.03  --abstr_ref_sig_restrict                funpre
% 3.84/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.03  --abstr_ref_under                       []
% 3.84/1.03  
% 3.84/1.03  ------ SAT Options
% 3.84/1.03  
% 3.84/1.03  --sat_mode                              false
% 3.84/1.03  --sat_fm_restart_options                ""
% 3.84/1.03  --sat_gr_def                            false
% 3.84/1.03  --sat_epr_types                         true
% 3.84/1.03  --sat_non_cyclic_types                  false
% 3.84/1.03  --sat_finite_models                     false
% 3.84/1.03  --sat_fm_lemmas                         false
% 3.84/1.03  --sat_fm_prep                           false
% 3.84/1.03  --sat_fm_uc_incr                        true
% 3.84/1.03  --sat_out_model                         small
% 3.84/1.03  --sat_out_clauses                       false
% 3.84/1.03  
% 3.84/1.03  ------ QBF Options
% 3.84/1.03  
% 3.84/1.03  --qbf_mode                              false
% 3.84/1.03  --qbf_elim_univ                         false
% 3.84/1.03  --qbf_dom_inst                          none
% 3.84/1.03  --qbf_dom_pre_inst                      false
% 3.84/1.03  --qbf_sk_in                             false
% 3.84/1.03  --qbf_pred_elim                         true
% 3.84/1.03  --qbf_split                             512
% 3.84/1.03  
% 3.84/1.03  ------ BMC1 Options
% 3.84/1.03  
% 3.84/1.03  --bmc1_incremental                      false
% 3.84/1.03  --bmc1_axioms                           reachable_all
% 3.84/1.03  --bmc1_min_bound                        0
% 3.84/1.03  --bmc1_max_bound                        -1
% 3.84/1.03  --bmc1_max_bound_default                -1
% 3.84/1.03  --bmc1_symbol_reachability              true
% 3.84/1.03  --bmc1_property_lemmas                  false
% 3.84/1.03  --bmc1_k_induction                      false
% 3.84/1.03  --bmc1_non_equiv_states                 false
% 3.84/1.03  --bmc1_deadlock                         false
% 3.84/1.03  --bmc1_ucm                              false
% 3.84/1.03  --bmc1_add_unsat_core                   none
% 3.84/1.03  --bmc1_unsat_core_children              false
% 3.84/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.03  --bmc1_out_stat                         full
% 3.84/1.03  --bmc1_ground_init                      false
% 3.84/1.03  --bmc1_pre_inst_next_state              false
% 3.84/1.03  --bmc1_pre_inst_state                   false
% 3.84/1.03  --bmc1_pre_inst_reach_state             false
% 3.84/1.03  --bmc1_out_unsat_core                   false
% 3.84/1.03  --bmc1_aig_witness_out                  false
% 3.84/1.03  --bmc1_verbose                          false
% 3.84/1.03  --bmc1_dump_clauses_tptp                false
% 3.84/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.03  --bmc1_dump_file                        -
% 3.84/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.03  --bmc1_ucm_extend_mode                  1
% 3.84/1.03  --bmc1_ucm_init_mode                    2
% 3.84/1.03  --bmc1_ucm_cone_mode                    none
% 3.84/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.03  --bmc1_ucm_relax_model                  4
% 3.84/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.03  --bmc1_ucm_layered_model                none
% 3.84/1.03  --bmc1_ucm_max_lemma_size               10
% 3.84/1.03  
% 3.84/1.03  ------ AIG Options
% 3.84/1.03  
% 3.84/1.03  --aig_mode                              false
% 3.84/1.03  
% 3.84/1.03  ------ Instantiation Options
% 3.84/1.03  
% 3.84/1.03  --instantiation_flag                    true
% 3.84/1.03  --inst_sos_flag                         true
% 3.84/1.03  --inst_sos_phase                        true
% 3.84/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel_side                     none
% 3.84/1.03  --inst_solver_per_active                1400
% 3.84/1.03  --inst_solver_calls_frac                1.
% 3.84/1.03  --inst_passive_queue_type               priority_queues
% 3.84/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.03  --inst_passive_queues_freq              [25;2]
% 3.84/1.03  --inst_dismatching                      true
% 3.84/1.03  --inst_eager_unprocessed_to_passive     true
% 3.84/1.03  --inst_prop_sim_given                   true
% 3.84/1.03  --inst_prop_sim_new                     false
% 3.84/1.03  --inst_subs_new                         false
% 3.84/1.03  --inst_eq_res_simp                      false
% 3.84/1.03  --inst_subs_given                       false
% 3.84/1.03  --inst_orphan_elimination               true
% 3.84/1.03  --inst_learning_loop_flag               true
% 3.84/1.03  --inst_learning_start                   3000
% 3.84/1.03  --inst_learning_factor                  2
% 3.84/1.03  --inst_start_prop_sim_after_learn       3
% 3.84/1.03  --inst_sel_renew                        solver
% 3.84/1.03  --inst_lit_activity_flag                true
% 3.84/1.03  --inst_restr_to_given                   false
% 3.84/1.03  --inst_activity_threshold               500
% 3.84/1.03  --inst_out_proof                        true
% 3.84/1.03  
% 3.84/1.03  ------ Resolution Options
% 3.84/1.03  
% 3.84/1.03  --resolution_flag                       false
% 3.84/1.03  --res_lit_sel                           adaptive
% 3.84/1.03  --res_lit_sel_side                      none
% 3.84/1.03  --res_ordering                          kbo
% 3.84/1.03  --res_to_prop_solver                    active
% 3.84/1.03  --res_prop_simpl_new                    false
% 3.84/1.03  --res_prop_simpl_given                  true
% 3.84/1.03  --res_passive_queue_type                priority_queues
% 3.84/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.03  --res_passive_queues_freq               [15;5]
% 3.84/1.03  --res_forward_subs                      full
% 3.84/1.03  --res_backward_subs                     full
% 3.84/1.03  --res_forward_subs_resolution           true
% 3.84/1.03  --res_backward_subs_resolution          true
% 3.84/1.03  --res_orphan_elimination                true
% 3.84/1.03  --res_time_limit                        2.
% 3.84/1.03  --res_out_proof                         true
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Options
% 3.84/1.03  
% 3.84/1.03  --superposition_flag                    true
% 3.84/1.03  --sup_passive_queue_type                priority_queues
% 3.84/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.03  --demod_completeness_check              fast
% 3.84/1.03  --demod_use_ground                      true
% 3.84/1.03  --sup_to_prop_solver                    passive
% 3.84/1.03  --sup_prop_simpl_new                    true
% 3.84/1.03  --sup_prop_simpl_given                  true
% 3.84/1.03  --sup_fun_splitting                     true
% 3.84/1.03  --sup_smt_interval                      50000
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Simplification Setup
% 3.84/1.03  
% 3.84/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_immed_triv                        [TrivRules]
% 3.84/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_bw_main                     []
% 3.84/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_input_bw                          []
% 3.84/1.03  
% 3.84/1.03  ------ Combination Options
% 3.84/1.03  
% 3.84/1.03  --comb_res_mult                         3
% 3.84/1.03  --comb_sup_mult                         2
% 3.84/1.03  --comb_inst_mult                        10
% 3.84/1.03  
% 3.84/1.03  ------ Debug Options
% 3.84/1.03  
% 3.84/1.03  --dbg_backtrace                         false
% 3.84/1.03  --dbg_dump_prop_clauses                 false
% 3.84/1.03  --dbg_dump_prop_clauses_file            -
% 3.84/1.03  --dbg_out_stat                          false
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  ------ Proving...
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  % SZS status Theorem for theBenchmark.p
% 3.84/1.03  
% 3.84/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.03  
% 3.84/1.03  fof(f11,axiom,(
% 3.84/1.03    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f34,plain,(
% 3.84/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.84/1.03    inference(nnf_transformation,[],[f11])).
% 3.84/1.03  
% 3.84/1.03  fof(f35,plain,(
% 3.84/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.84/1.03    inference(flattening,[],[f34])).
% 3.84/1.03  
% 3.84/1.03  fof(f60,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f35])).
% 3.84/1.03  
% 3.84/1.03  fof(f9,axiom,(
% 3.84/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f56,plain,(
% 3.84/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f9])).
% 3.84/1.03  
% 3.84/1.03  fof(f10,axiom,(
% 3.84/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f57,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f10])).
% 3.84/1.03  
% 3.84/1.03  fof(f64,plain,(
% 3.84/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.84/1.03    inference(definition_unfolding,[],[f56,f57])).
% 3.84/1.03  
% 3.84/1.03  fof(f66,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.84/1.03    inference(definition_unfolding,[],[f60,f64])).
% 3.84/1.03  
% 3.84/1.03  fof(f1,axiom,(
% 3.84/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f14,plain,(
% 3.84/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.84/1.03    inference(ennf_transformation,[],[f1])).
% 3.84/1.03  
% 3.84/1.03  fof(f18,plain,(
% 3.84/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.84/1.03    inference(nnf_transformation,[],[f14])).
% 3.84/1.03  
% 3.84/1.03  fof(f19,plain,(
% 3.84/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.84/1.03    inference(rectify,[],[f18])).
% 3.84/1.03  
% 3.84/1.03  fof(f20,plain,(
% 3.84/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.84/1.03    introduced(choice_axiom,[])).
% 3.84/1.03  
% 3.84/1.03  fof(f21,plain,(
% 3.84/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.84/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.84/1.03  
% 3.84/1.03  fof(f39,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f21])).
% 3.84/1.03  
% 3.84/1.03  fof(f12,conjecture,(
% 3.84/1.03    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f13,negated_conjecture,(
% 3.84/1.03    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.84/1.03    inference(negated_conjecture,[],[f12])).
% 3.84/1.03  
% 3.84/1.03  fof(f17,plain,(
% 3.84/1.03    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.84/1.03    inference(ennf_transformation,[],[f13])).
% 3.84/1.03  
% 3.84/1.03  fof(f36,plain,(
% 3.84/1.03    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK5 = X2 | ~r2_hidden(X2,sK4)) & k1_xboole_0 != sK4 & k1_tarski(sK5) != sK4)),
% 3.84/1.03    introduced(choice_axiom,[])).
% 3.84/1.03  
% 3.84/1.03  fof(f37,plain,(
% 3.84/1.03    ! [X2] : (sK5 = X2 | ~r2_hidden(X2,sK4)) & k1_xboole_0 != sK4 & k1_tarski(sK5) != sK4),
% 3.84/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f36])).
% 3.84/1.03  
% 3.84/1.03  fof(f63,plain,(
% 3.84/1.03    ( ! [X2] : (sK5 = X2 | ~r2_hidden(X2,sK4)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f37])).
% 3.84/1.03  
% 3.84/1.03  fof(f5,axiom,(
% 3.84/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f32,plain,(
% 3.84/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/1.03    inference(nnf_transformation,[],[f5])).
% 3.84/1.03  
% 3.84/1.03  fof(f33,plain,(
% 3.84/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/1.03    inference(flattening,[],[f32])).
% 3.84/1.03  
% 3.84/1.03  fof(f52,plain,(
% 3.84/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f33])).
% 3.84/1.03  
% 3.84/1.03  fof(f51,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.84/1.03    inference(cnf_transformation,[],[f33])).
% 3.84/1.03  
% 3.84/1.03  fof(f73,plain,(
% 3.84/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/1.03    inference(equality_resolution,[],[f51])).
% 3.84/1.03  
% 3.84/1.03  fof(f4,axiom,(
% 3.84/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f16,plain,(
% 3.84/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.84/1.03    inference(ennf_transformation,[],[f4])).
% 3.84/1.03  
% 3.84/1.03  fof(f30,plain,(
% 3.84/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.84/1.03    introduced(choice_axiom,[])).
% 3.84/1.03  
% 3.84/1.03  fof(f31,plain,(
% 3.84/1.03    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 3.84/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f30])).
% 3.84/1.03  
% 3.84/1.03  fof(f49,plain,(
% 3.84/1.03    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.84/1.03    inference(cnf_transformation,[],[f31])).
% 3.84/1.03  
% 3.84/1.03  fof(f58,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f35])).
% 3.84/1.03  
% 3.84/1.03  fof(f68,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 3.84/1.03    inference(definition_unfolding,[],[f58,f64])).
% 3.84/1.03  
% 3.84/1.03  fof(f40,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f21])).
% 3.84/1.03  
% 3.84/1.03  fof(f6,axiom,(
% 3.84/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f53,plain,(
% 3.84/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f6])).
% 3.84/1.03  
% 3.84/1.03  fof(f50,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/1.03    inference(cnf_transformation,[],[f33])).
% 3.84/1.03  
% 3.84/1.03  fof(f74,plain,(
% 3.84/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/1.03    inference(equality_resolution,[],[f50])).
% 3.84/1.03  
% 3.84/1.03  fof(f62,plain,(
% 3.84/1.03    k1_xboole_0 != sK4),
% 3.84/1.03    inference(cnf_transformation,[],[f37])).
% 3.84/1.03  
% 3.84/1.03  fof(f61,plain,(
% 3.84/1.03    k1_tarski(sK5) != sK4),
% 3.84/1.03    inference(cnf_transformation,[],[f37])).
% 3.84/1.03  
% 3.84/1.03  fof(f8,axiom,(
% 3.84/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f55,plain,(
% 3.84/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f8])).
% 3.84/1.03  
% 3.84/1.03  fof(f65,plain,(
% 3.84/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.84/1.03    inference(definition_unfolding,[],[f55,f64])).
% 3.84/1.03  
% 3.84/1.03  fof(f69,plain,(
% 3.84/1.03    k2_enumset1(sK5,sK5,sK5,sK5) != sK4),
% 3.84/1.03    inference(definition_unfolding,[],[f61,f65])).
% 3.84/1.03  
% 3.84/1.03  cnf(c_352,plain,
% 3.84/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.84/1.03      theory(equality) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1926,plain,
% 3.84/1.03      ( ~ r2_hidden(X0,X1)
% 3.84/1.03      | r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.03      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 3.84/1.03      | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != X0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_352]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_4047,plain,
% 3.84/1.03      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.03      | r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.03      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 3.84/1.03      | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != X0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_4049,plain,
% 3.84/1.03      ( r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.03      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.03      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 3.84/1.03      | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_4047]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_17,plain,
% 3.84/1.03      ( ~ r2_hidden(X0,X1)
% 3.84/1.03      | ~ r2_hidden(X2,X1)
% 3.84/1.03      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 3.84/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_652,plain,
% 3.84/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.84/1.03      | r2_hidden(X2,X1) != iProver_top
% 3.84/1.03      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1,plain,
% 3.84/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.84/1.03      inference(cnf_transformation,[],[f39]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_666,plain,
% 3.84/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.84/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_20,negated_conjecture,
% 3.84/1.03      ( ~ r2_hidden(X0,sK4) | sK5 = X0 ),
% 3.84/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_649,plain,
% 3.84/1.03      ( sK5 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1357,plain,
% 3.84/1.03      ( sK0(sK4,X0) = sK5 | r1_tarski(sK4,X0) = iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_666,c_649]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_12,plain,
% 3.84/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.84/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_655,plain,
% 3.84/1.03      ( X0 = X1
% 3.84/1.03      | r1_tarski(X1,X0) != iProver_top
% 3.84/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2151,plain,
% 3.84/1.03      ( sK0(sK4,X0) = sK5 | sK4 = X0 | r1_tarski(X0,sK4) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1357,c_655]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_3098,plain,
% 3.84/1.04      ( k2_enumset1(X0,X0,X0,X1) = sK4
% 3.84/1.04      | sK0(sK4,k2_enumset1(X0,X0,X0,X1)) = sK5
% 3.84/1.04      | r2_hidden(X1,sK4) != iProver_top
% 3.84/1.04      | r2_hidden(X0,sK4) != iProver_top ),
% 3.84/1.04      inference(superposition,[status(thm)],[c_652,c_2151]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_3103,plain,
% 3.84/1.04      ( k2_enumset1(sK5,sK5,sK5,sK5) = sK4
% 3.84/1.04      | sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 3.84/1.04      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_3098]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_13,plain,
% 3.84/1.04      ( r1_tarski(X0,X0) ),
% 3.84/1.04      inference(cnf_transformation,[],[f73]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1751,plain,
% 3.84/1.04      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_11,plain,
% 3.84/1.04      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 3.84/1.04      inference(cnf_transformation,[],[f49]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_656,plain,
% 3.84/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 3.84/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1351,plain,
% 3.84/1.04      ( sK3(sK4) = sK5 | sK4 = k1_xboole_0 ),
% 3.84/1.04      inference(superposition,[status(thm)],[c_656,c_649]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1467,plain,
% 3.84/1.04      ( sK4 = k1_xboole_0 | r2_hidden(sK5,sK4) = iProver_top ),
% 3.84/1.04      inference(superposition,[status(thm)],[c_1351,c_656]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1468,plain,
% 3.84/1.04      ( r2_hidden(sK5,sK4) | sK4 = k1_xboole_0 ),
% 3.84/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1467]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_351,plain,
% 3.84/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.84/1.04      theory(equality) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_767,plain,
% 3.84/1.04      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.84/1.04      | r1_tarski(sK4,k1_xboole_0)
% 3.84/1.04      | sK4 != X0 ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_351]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1314,plain,
% 3.84/1.04      ( r1_tarski(sK4,k1_xboole_0)
% 3.84/1.04      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.84/1.04      | sK4 != k1_xboole_0 ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_767]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_654,plain,
% 3.84/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 3.84/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_19,plain,
% 3.84/1.04      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
% 3.84/1.04      inference(cnf_transformation,[],[f68]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_650,plain,
% 3.84/1.04      ( r2_hidden(X0,X1) = iProver_top
% 3.84/1.04      | r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) != iProver_top ),
% 3.84/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1252,plain,
% 3.84/1.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.84/1.04      inference(superposition,[status(thm)],[c_654,c_650]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1253,plain,
% 3.84/1.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.84/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1252]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_1255,plain,
% 3.84/1.04      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_1253]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_0,plain,
% 3.84/1.04      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.84/1.04      inference(cnf_transformation,[],[f40]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_890,plain,
% 3.84/1.04      ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.04      | r1_tarski(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_15,plain,
% 3.84/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 3.84/1.04      inference(cnf_transformation,[],[f53]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_886,plain,
% 3.84/1.04      ( r1_tarski(k1_xboole_0,sK4) ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_15]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_818,plain,
% 3.84/1.04      ( ~ r2_hidden(sK5,sK4)
% 3.84/1.04      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_17]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_708,plain,
% 3.84/1.04      ( ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4)
% 3.84/1.04      | ~ r1_tarski(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.84/1.04      | k2_enumset1(sK5,sK5,sK5,sK5) = sK4 ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_690,plain,
% 3.84/1.04      ( ~ r1_tarski(sK4,k1_xboole_0)
% 3.84/1.04      | ~ r1_tarski(k1_xboole_0,sK4)
% 3.84/1.04      | k1_xboole_0 = sK4 ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_354,plain,
% 3.84/1.04      ( X0 != X1
% 3.84/1.04      | X2 != X3
% 3.84/1.04      | X4 != X5
% 3.84/1.04      | X6 != X7
% 3.84/1.04      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 3.84/1.04      theory(equality) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_358,plain,
% 3.84/1.04      ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK5,sK5,sK5,sK5)
% 3.84/1.04      | sK5 != sK5 ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_354]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_42,plain,
% 3.84/1.04      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_14,plain,
% 3.84/1.04      ( r1_tarski(X0,X0) ),
% 3.84/1.04      inference(cnf_transformation,[],[f74]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_38,plain,
% 3.84/1.04      ( r1_tarski(sK5,sK5) ),
% 3.84/1.04      inference(instantiation,[status(thm)],[c_14]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_21,negated_conjecture,
% 3.84/1.04      ( k1_xboole_0 != sK4 ),
% 3.84/1.04      inference(cnf_transformation,[],[f62]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(c_22,negated_conjecture,
% 3.84/1.04      ( k2_enumset1(sK5,sK5,sK5,sK5) != sK4 ),
% 3.84/1.04      inference(cnf_transformation,[],[f69]) ).
% 3.84/1.04  
% 3.84/1.04  cnf(contradiction,plain,
% 3.84/1.04      ( $false ),
% 3.84/1.04      inference(minisat,
% 3.84/1.04                [status(thm)],
% 3.84/1.04                [c_4049,c_3103,c_1751,c_1468,c_1467,c_1314,c_1255,c_890,
% 3.84/1.04                 c_886,c_818,c_708,c_690,c_358,c_42,c_38,c_21,c_22]) ).
% 3.84/1.04  
% 3.84/1.04  
% 3.84/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.04  
% 3.84/1.04  ------                               Statistics
% 3.84/1.04  
% 3.84/1.04  ------ General
% 3.84/1.04  
% 3.84/1.04  abstr_ref_over_cycles:                  0
% 3.84/1.04  abstr_ref_under_cycles:                 0
% 3.84/1.04  gc_basic_clause_elim:                   0
% 3.84/1.04  forced_gc_time:                         0
% 3.84/1.04  parsing_time:                           0.011
% 3.84/1.04  unif_index_cands_time:                  0.
% 3.84/1.04  unif_index_add_time:                    0.
% 3.84/1.04  orderings_time:                         0.
% 3.84/1.04  out_proof_time:                         0.011
% 3.84/1.04  total_time:                             0.187
% 3.84/1.04  num_of_symbols:                         42
% 3.84/1.04  num_of_terms:                           4426
% 3.84/1.04  
% 3.84/1.04  ------ Preprocessing
% 3.84/1.04  
% 3.84/1.04  num_of_splits:                          0
% 3.84/1.04  num_of_split_atoms:                     0
% 3.84/1.04  num_of_reused_defs:                     0
% 3.84/1.04  num_eq_ax_congr_red:                    30
% 3.84/1.04  num_of_sem_filtered_clauses:            1
% 3.84/1.04  num_of_subtypes:                        0
% 3.84/1.04  monotx_restored_types:                  0
% 3.84/1.04  sat_num_of_epr_types:                   0
% 3.84/1.04  sat_num_of_non_cyclic_types:            0
% 3.84/1.04  sat_guarded_non_collapsed_types:        0
% 3.84/1.04  num_pure_diseq_elim:                    0
% 3.84/1.04  simp_replaced_by:                       0
% 3.84/1.04  res_preprocessed:                       101
% 3.84/1.04  prep_upred:                             0
% 3.84/1.04  prep_unflattend:                        0
% 3.84/1.04  smt_new_axioms:                         0
% 3.84/1.04  pred_elim_cands:                        2
% 3.84/1.04  pred_elim:                              0
% 3.84/1.04  pred_elim_cl:                           0
% 3.84/1.04  pred_elim_cycles:                       2
% 3.84/1.04  merged_defs:                            0
% 3.84/1.04  merged_defs_ncl:                        0
% 3.84/1.04  bin_hyper_res:                          0
% 3.84/1.04  prep_cycles:                            4
% 3.84/1.04  pred_elim_time:                         0.
% 3.84/1.04  splitting_time:                         0.
% 3.84/1.04  sem_filter_time:                        0.
% 3.84/1.04  monotx_time:                            0.
% 3.84/1.04  subtype_inf_time:                       0.
% 3.84/1.04  
% 3.84/1.04  ------ Problem properties
% 3.84/1.04  
% 3.84/1.04  clauses:                                22
% 3.84/1.04  conjectures:                            3
% 3.84/1.04  epr:                                    6
% 3.84/1.04  horn:                                   15
% 3.84/1.04  ground:                                 2
% 3.84/1.04  unary:                                  5
% 3.84/1.04  binary:                                 8
% 3.84/1.04  lits:                                   49
% 3.84/1.04  lits_eq:                                11
% 3.84/1.04  fd_pure:                                0
% 3.84/1.04  fd_pseudo:                              0
% 3.84/1.04  fd_cond:                                2
% 3.84/1.04  fd_pseudo_cond:                         6
% 3.84/1.04  ac_symbols:                             0
% 3.84/1.04  
% 3.84/1.04  ------ Propositional Solver
% 3.84/1.04  
% 3.84/1.04  prop_solver_calls:                      28
% 3.84/1.04  prop_fast_solver_calls:                 586
% 3.84/1.04  smt_solver_calls:                       0
% 3.84/1.04  smt_fast_solver_calls:                  0
% 3.84/1.04  prop_num_of_clauses:                    2053
% 3.84/1.04  prop_preprocess_simplified:             5905
% 3.84/1.04  prop_fo_subsumed:                       5
% 3.84/1.04  prop_solver_time:                       0.
% 3.84/1.04  smt_solver_time:                        0.
% 3.84/1.04  smt_fast_solver_time:                   0.
% 3.84/1.04  prop_fast_solver_time:                  0.
% 3.84/1.04  prop_unsat_core_time:                   0.
% 3.84/1.04  
% 3.84/1.04  ------ QBF
% 3.84/1.04  
% 3.84/1.04  qbf_q_res:                              0
% 3.84/1.04  qbf_num_tautologies:                    0
% 3.84/1.04  qbf_prep_cycles:                        0
% 3.84/1.04  
% 3.84/1.04  ------ BMC1
% 3.84/1.04  
% 3.84/1.04  bmc1_current_bound:                     -1
% 3.84/1.04  bmc1_last_solved_bound:                 -1
% 3.84/1.04  bmc1_unsat_core_size:                   -1
% 3.84/1.04  bmc1_unsat_core_parents_size:           -1
% 3.84/1.04  bmc1_merge_next_fun:                    0
% 3.84/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.84/1.04  
% 3.84/1.04  ------ Instantiation
% 3.84/1.04  
% 3.84/1.04  inst_num_of_clauses:                    500
% 3.84/1.04  inst_num_in_passive:                    157
% 3.84/1.04  inst_num_in_active:                     187
% 3.84/1.04  inst_num_in_unprocessed:                155
% 3.84/1.04  inst_num_of_loops:                      255
% 3.84/1.04  inst_num_of_learning_restarts:          0
% 3.84/1.04  inst_num_moves_active_passive:          67
% 3.84/1.04  inst_lit_activity:                      0
% 3.84/1.04  inst_lit_activity_moves:                0
% 3.84/1.04  inst_num_tautologies:                   0
% 3.84/1.04  inst_num_prop_implied:                  0
% 3.84/1.04  inst_num_existing_simplified:           0
% 3.84/1.04  inst_num_eq_res_simplified:             0
% 3.84/1.04  inst_num_child_elim:                    0
% 3.84/1.04  inst_num_of_dismatching_blockings:      97
% 3.84/1.04  inst_num_of_non_proper_insts:           488
% 3.84/1.04  inst_num_of_duplicates:                 0
% 3.84/1.04  inst_inst_num_from_inst_to_res:         0
% 3.84/1.04  inst_dismatching_checking_time:         0.
% 3.84/1.04  
% 3.84/1.04  ------ Resolution
% 3.84/1.04  
% 3.84/1.04  res_num_of_clauses:                     0
% 3.84/1.04  res_num_in_passive:                     0
% 3.84/1.04  res_num_in_active:                      0
% 3.84/1.04  res_num_of_loops:                       105
% 3.84/1.04  res_forward_subset_subsumed:            36
% 3.84/1.04  res_backward_subset_subsumed:           0
% 3.84/1.04  res_forward_subsumed:                   0
% 3.84/1.04  res_backward_subsumed:                  0
% 3.84/1.04  res_forward_subsumption_resolution:     0
% 3.84/1.04  res_backward_subsumption_resolution:    0
% 3.84/1.04  res_clause_to_clause_subsumption:       360
% 3.84/1.04  res_orphan_elimination:                 0
% 3.84/1.04  res_tautology_del:                      37
% 3.84/1.04  res_num_eq_res_simplified:              0
% 3.84/1.04  res_num_sel_changes:                    0
% 3.84/1.04  res_moves_from_active_to_pass:          0
% 3.84/1.04  
% 3.84/1.04  ------ Superposition
% 3.84/1.04  
% 3.84/1.04  sup_time_total:                         0.
% 3.84/1.04  sup_time_generating:                    0.
% 3.84/1.04  sup_time_sim_full:                      0.
% 3.84/1.04  sup_time_sim_immed:                     0.
% 3.84/1.04  
% 3.84/1.04  sup_num_of_clauses:                     125
% 3.84/1.04  sup_num_in_active:                      48
% 3.84/1.04  sup_num_in_passive:                     77
% 3.84/1.04  sup_num_of_loops:                       50
% 3.84/1.04  sup_fw_superposition:                   65
% 3.84/1.04  sup_bw_superposition:                   107
% 3.84/1.04  sup_immediate_simplified:               34
% 3.84/1.04  sup_given_eliminated:                   1
% 3.84/1.04  comparisons_done:                       0
% 3.84/1.04  comparisons_avoided:                    28
% 3.84/1.04  
% 3.84/1.04  ------ Simplifications
% 3.84/1.04  
% 3.84/1.04  
% 3.84/1.04  sim_fw_subset_subsumed:                 12
% 3.84/1.04  sim_bw_subset_subsumed:                 1
% 3.84/1.04  sim_fw_subsumed:                        14
% 3.84/1.04  sim_bw_subsumed:                        2
% 3.84/1.04  sim_fw_subsumption_res:                 0
% 3.84/1.04  sim_bw_subsumption_res:                 0
% 3.84/1.04  sim_tautology_del:                      10
% 3.84/1.04  sim_eq_tautology_del:                   15
% 3.84/1.04  sim_eq_res_simp:                        1
% 3.84/1.04  sim_fw_demodulated:                     8
% 3.84/1.04  sim_bw_demodulated:                     0
% 3.84/1.04  sim_light_normalised:                   8
% 3.84/1.04  sim_joinable_taut:                      0
% 3.84/1.04  sim_joinable_simp:                      0
% 3.84/1.04  sim_ac_normalised:                      0
% 3.84/1.04  sim_smt_subsumption:                    0
% 3.84/1.04  
%------------------------------------------------------------------------------
