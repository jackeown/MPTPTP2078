%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:35 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 161 expanded)
%              Number of clauses        :   28 (  35 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 ( 525 expanded)
%              Number of equality atoms :  135 ( 344 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f69,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK2,sK4)
      & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,sK4)
    & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f36])).

fof(f63,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f83,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f82])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_406,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_610,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_406])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_404,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_402,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_414,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2304,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r2_xboole_0(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_402,c_414])).

cnf(c_6,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_413,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2791,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2304,c_413])).

cnf(c_2796,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_2791])).

cnf(c_11,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_408,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_821,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_408])).

cnf(c_2956,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2796,c_821])).

cnf(c_2959,plain,
    ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_404])).

cnf(c_3251,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_2959])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_415,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3966,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_415])).

cnf(c_9135,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_3966])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9135,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.97/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/1.00  
% 3.97/1.00  ------  iProver source info
% 3.97/1.00  
% 3.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/1.00  git: non_committed_changes: false
% 3.97/1.00  git: last_make_outside_of_git: false
% 3.97/1.00  
% 3.97/1.00  ------ 
% 3.97/1.00  ------ Parsing...
% 3.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.00  ------ Proving...
% 3.97/1.00  ------ Problem Properties 
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  clauses                                 20
% 3.97/1.00  conjectures                             2
% 3.97/1.00  EPR                                     4
% 3.97/1.00  Horn                                    16
% 3.97/1.00  unary                                   9
% 3.97/1.00  binary                                  4
% 3.97/1.00  lits                                    41
% 3.97/1.00  lits eq                                 18
% 3.97/1.00  fd_pure                                 0
% 3.97/1.00  fd_pseudo                               0
% 3.97/1.00  fd_cond                                 0
% 3.97/1.00  fd_pseudo_cond                          5
% 3.97/1.00  AC symbols                              0
% 3.97/1.00  
% 3.97/1.00  ------ Input Options Time Limit: Unbounded
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  ------ 
% 3.97/1.00  Current options:
% 3.97/1.00  ------ 
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  ------ Proving...
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  % SZS status Theorem for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  fof(f9,axiom,(
% 3.97/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f55,plain,(
% 3.97/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f9])).
% 3.97/1.00  
% 3.97/1.00  fof(f10,axiom,(
% 3.97/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f56,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f10])).
% 3.97/1.00  
% 3.97/1.00  fof(f11,axiom,(
% 3.97/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f57,plain,(
% 3.97/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f11])).
% 3.97/1.00  
% 3.97/1.00  fof(f12,axiom,(
% 3.97/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f58,plain,(
% 3.97/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f12])).
% 3.97/1.00  
% 3.97/1.00  fof(f65,plain,(
% 3.97/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f57,f58])).
% 3.97/1.00  
% 3.97/1.00  fof(f66,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f56,f65])).
% 3.97/1.00  
% 3.97/1.00  fof(f69,plain,(
% 3.97/1.00    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f55,f66])).
% 3.97/1.00  
% 3.97/1.00  fof(f4,axiom,(
% 3.97/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f24,plain,(
% 3.97/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.97/1.00    inference(ennf_transformation,[],[f4])).
% 3.97/1.00  
% 3.97/1.00  fof(f31,plain,(
% 3.97/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.97/1.00    inference(nnf_transformation,[],[f24])).
% 3.97/1.00  
% 3.97/1.00  fof(f32,plain,(
% 3.97/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.97/1.00    inference(flattening,[],[f31])).
% 3.97/1.00  
% 3.97/1.00  fof(f33,plain,(
% 3.97/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.97/1.00    inference(rectify,[],[f32])).
% 3.97/1.00  
% 3.97/1.00  fof(f34,plain,(
% 3.97/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f35,plain,(
% 3.97/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.97/1.00  
% 3.97/1.00  fof(f44,plain,(
% 3.97/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.97/1.00    inference(cnf_transformation,[],[f35])).
% 3.97/1.00  
% 3.97/1.00  fof(f77,plain,(
% 3.97/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 3.97/1.00    inference(definition_unfolding,[],[f44,f66])).
% 3.97/1.00  
% 3.97/1.00  fof(f86,plain,(
% 3.97/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3) )),
% 3.97/1.00    inference(equality_resolution,[],[f77])).
% 3.97/1.00  
% 3.97/1.00  fof(f87,plain,(
% 3.97/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2))) )),
% 3.97/1.00    inference(equality_resolution,[],[f86])).
% 3.97/1.00  
% 3.97/1.00  fof(f15,axiom,(
% 3.97/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f25,plain,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.97/1.00    inference(ennf_transformation,[],[f15])).
% 3.97/1.00  
% 3.97/1.00  fof(f61,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f25])).
% 3.97/1.00  
% 3.97/1.00  fof(f17,conjecture,(
% 3.97/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f18,negated_conjecture,(
% 3.97/1.00    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.97/1.00    inference(negated_conjecture,[],[f17])).
% 3.97/1.00  
% 3.97/1.00  fof(f26,plain,(
% 3.97/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.97/1.00    inference(ennf_transformation,[],[f18])).
% 3.97/1.00  
% 3.97/1.00  fof(f36,plain,(
% 3.97/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f37,plain,(
% 3.97/1.00    ~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f36])).
% 3.97/1.00  
% 3.97/1.00  fof(f63,plain,(
% 3.97/1.00    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 3.97/1.00    inference(cnf_transformation,[],[f37])).
% 3.97/1.00  
% 3.97/1.00  fof(f16,axiom,(
% 3.97/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f62,plain,(
% 3.97/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.97/1.00    inference(cnf_transformation,[],[f16])).
% 3.97/1.00  
% 3.97/1.00  fof(f81,plain,(
% 3.97/1.00    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4)),
% 3.97/1.00    inference(definition_unfolding,[],[f63,f62])).
% 3.97/1.00  
% 3.97/1.00  fof(f2,axiom,(
% 3.97/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f19,plain,(
% 3.97/1.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.97/1.00    inference(unused_predicate_definition_removal,[],[f2])).
% 3.97/1.00  
% 3.97/1.00  fof(f21,plain,(
% 3.97/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(ennf_transformation,[],[f19])).
% 3.97/1.00  
% 3.97/1.00  fof(f22,plain,(
% 3.97/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.97/1.00    inference(flattening,[],[f21])).
% 3.97/1.00  
% 3.97/1.00  fof(f41,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f22])).
% 3.97/1.00  
% 3.97/1.00  fof(f3,axiom,(
% 3.97/1.00    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f23,plain,(
% 3.97/1.00    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 3.97/1.00    inference(ennf_transformation,[],[f3])).
% 3.97/1.00  
% 3.97/1.00  fof(f42,plain,(
% 3.97/1.00    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f23])).
% 3.97/1.00  
% 3.97/1.00  fof(f46,plain,(
% 3.97/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.97/1.00    inference(cnf_transformation,[],[f35])).
% 3.97/1.00  
% 3.97/1.00  fof(f75,plain,(
% 3.97/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 3.97/1.00    inference(definition_unfolding,[],[f46,f66])).
% 3.97/1.00  
% 3.97/1.00  fof(f82,plain,(
% 3.97/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3) )),
% 3.97/1.00    inference(equality_resolution,[],[f75])).
% 3.97/1.00  
% 3.97/1.00  fof(f83,plain,(
% 3.97/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5))) )),
% 3.97/1.00    inference(equality_resolution,[],[f82])).
% 3.97/1.00  
% 3.97/1.00  fof(f1,axiom,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f20,plain,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.97/1.00    inference(ennf_transformation,[],[f1])).
% 3.97/1.00  
% 3.97/1.00  fof(f27,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(nnf_transformation,[],[f20])).
% 3.97/1.00  
% 3.97/1.00  fof(f28,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(rectify,[],[f27])).
% 3.97/1.00  
% 3.97/1.00  fof(f29,plain,(
% 3.97/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f30,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.97/1.00  
% 3.97/1.00  fof(f38,plain,(
% 3.97/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f30])).
% 3.97/1.00  
% 3.97/1.00  fof(f64,plain,(
% 3.97/1.00    ~r2_hidden(sK2,sK4)),
% 3.97/1.00    inference(cnf_transformation,[],[f37])).
% 3.97/1.00  
% 3.97/1.00  cnf(c_0,plain,
% 3.97/1.00      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_13,plain,
% 3.97/1.00      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_406,plain,
% 3.97/1.00      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_610,plain,
% 3.97/1.00      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_0,c_406]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_17,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_404,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_19,negated_conjecture,
% 3.97/1.00      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
% 3.97/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_402,plain,
% 3.97/1.00      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5,plain,
% 3.97/1.00      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 3.97/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_414,plain,
% 3.97/1.00      ( X0 = X1
% 3.97/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2304,plain,
% 3.97/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 3.97/1.00      | r2_xboole_0(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_402,c_414]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6,plain,
% 3.97/1.00      ( ~ r2_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_413,plain,
% 3.97/1.00      ( r2_xboole_0(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2791,plain,
% 3.97/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 3.97/1.00      | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_2304,c_413]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2796,plain,
% 3.97/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 3.97/1.00      | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_404,c_2791]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_11,plain,
% 3.97/1.00      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_408,plain,
% 3.97/1.00      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_821,plain,
% 3.97/1.00      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_0,c_408]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2956,plain,
% 3.97/1.00      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
% 3.97/1.00      inference(forward_subsumption_resolution,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_2796,c_821]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2959,plain,
% 3.97/1.00      ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(X0,sK4) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_2956,c_404]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3251,plain,
% 3.97/1.00      ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_610,c_2959]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.97/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_415,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.97/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3966,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.97/1.00      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_610,c_415]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_9135,plain,
% 3.97/1.00      ( r2_hidden(sK2,sK4) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_3251,c_3966]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_18,negated_conjecture,
% 3.97/1.00      ( ~ r2_hidden(sK2,sK4) ),
% 3.97/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_21,plain,
% 3.97/1.00      ( r2_hidden(sK2,sK4) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(contradiction,plain,
% 3.97/1.00      ( $false ),
% 3.97/1.00      inference(minisat,[status(thm)],[c_9135,c_21]) ).
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  ------                               Statistics
% 3.97/1.00  
% 3.97/1.00  ------ Selected
% 3.97/1.00  
% 3.97/1.00  total_time:                             0.503
% 3.97/1.00  
%------------------------------------------------------------------------------
