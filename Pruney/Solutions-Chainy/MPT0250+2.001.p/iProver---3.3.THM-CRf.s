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
% DateTime   : Thu Dec  3 11:32:42 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 168 expanded)
%              Number of clauses        :   32 (  39 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 ( 438 expanded)
%              Number of equality atoms :  142 ( 287 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(definition_unfolding,[],[f44,f50,f45])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) != X3 ) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2))) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f76,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2)))) ),
    inference(equality_resolution,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X3,X2),k2_tarski(X1,X0))) ),
    inference(definition_unfolding,[],[f43,f57,f57])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK1,sK2)
      & r1_tarski(k2_xboole_0(k1_tarski(sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK2)
    & r1_tarski(k2_xboole_0(k1_tarski(sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f30])).

fof(f54,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f54,f50,f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) != X3 ) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f71,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X5,X5))) != X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f72,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X5,X5)))) ),
    inference(equality_resolution,[],[f71])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_567,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_765,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_567])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_565,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_574,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9187,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(X1,X0) != iProver_top
    | r2_xboole_0(X1,k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_574])).

cnf(c_11,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X3,X2),k2_tarski(X1,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1060,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_1502,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_1060,c_0])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_560,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1579,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1502,c_560])).

cnf(c_9189,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2
    | r2_xboole_0(k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_574])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_575,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9668,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2
    | r2_xboole_0(sK2,k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9189,c_575])).

cnf(c_49882,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2
    | r2_hidden(sK2,k2_tarski(sK2,k2_tarski(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9187,c_9668])).

cnf(c_50030,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_765,c_49882])).

cnf(c_7,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_569,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_933,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_569])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_563,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3131,plain,
    ( r2_hidden(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(k2_tarski(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_563])).

cnf(c_12208,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X2,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_3131])).

cnf(c_50035,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_50030,c_12208])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50035,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.78/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.78/2.01  
% 11.78/2.01  ------  iProver source info
% 11.78/2.01  
% 11.78/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.78/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.78/2.01  git: non_committed_changes: false
% 11.78/2.01  git: last_make_outside_of_git: false
% 11.78/2.01  
% 11.78/2.01  ------ 
% 11.78/2.01  
% 11.78/2.01  ------ Input Options
% 11.78/2.01  
% 11.78/2.01  --out_options                           all
% 11.78/2.01  --tptp_safe_out                         true
% 11.78/2.01  --problem_path                          ""
% 11.78/2.01  --include_path                          ""
% 11.78/2.01  --clausifier                            res/vclausify_rel
% 11.78/2.01  --clausifier_options                    ""
% 11.78/2.01  --stdin                                 false
% 11.78/2.01  --stats_out                             all
% 11.78/2.01  
% 11.78/2.01  ------ General Options
% 11.78/2.01  
% 11.78/2.01  --fof                                   false
% 11.78/2.01  --time_out_real                         305.
% 11.78/2.01  --time_out_virtual                      -1.
% 11.78/2.01  --symbol_type_check                     false
% 11.78/2.01  --clausify_out                          false
% 11.78/2.01  --sig_cnt_out                           false
% 11.78/2.01  --trig_cnt_out                          false
% 11.78/2.01  --trig_cnt_out_tolerance                1.
% 11.78/2.01  --trig_cnt_out_sk_spl                   false
% 11.78/2.01  --abstr_cl_out                          false
% 11.78/2.01  
% 11.78/2.01  ------ Global Options
% 11.78/2.01  
% 11.78/2.01  --schedule                              default
% 11.78/2.01  --add_important_lit                     false
% 11.78/2.01  --prop_solver_per_cl                    1000
% 11.78/2.01  --min_unsat_core                        false
% 11.78/2.01  --soft_assumptions                      false
% 11.78/2.01  --soft_lemma_size                       3
% 11.78/2.01  --prop_impl_unit_size                   0
% 11.78/2.01  --prop_impl_unit                        []
% 11.78/2.01  --share_sel_clauses                     true
% 11.78/2.01  --reset_solvers                         false
% 11.78/2.01  --bc_imp_inh                            [conj_cone]
% 11.78/2.01  --conj_cone_tolerance                   3.
% 11.78/2.01  --extra_neg_conj                        none
% 11.78/2.01  --large_theory_mode                     true
% 11.78/2.01  --prolific_symb_bound                   200
% 11.78/2.01  --lt_threshold                          2000
% 11.78/2.01  --clause_weak_htbl                      true
% 11.78/2.01  --gc_record_bc_elim                     false
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing Options
% 11.78/2.01  
% 11.78/2.01  --preprocessing_flag                    true
% 11.78/2.01  --time_out_prep_mult                    0.1
% 11.78/2.01  --splitting_mode                        input
% 11.78/2.01  --splitting_grd                         true
% 11.78/2.01  --splitting_cvd                         false
% 11.78/2.01  --splitting_cvd_svl                     false
% 11.78/2.01  --splitting_nvd                         32
% 11.78/2.01  --sub_typing                            true
% 11.78/2.01  --prep_gs_sim                           true
% 11.78/2.01  --prep_unflatten                        true
% 11.78/2.01  --prep_res_sim                          true
% 11.78/2.01  --prep_upred                            true
% 11.78/2.01  --prep_sem_filter                       exhaustive
% 11.78/2.01  --prep_sem_filter_out                   false
% 11.78/2.01  --pred_elim                             true
% 11.78/2.01  --res_sim_input                         true
% 11.78/2.01  --eq_ax_congr_red                       true
% 11.78/2.01  --pure_diseq_elim                       true
% 11.78/2.01  --brand_transform                       false
% 11.78/2.01  --non_eq_to_eq                          false
% 11.78/2.01  --prep_def_merge                        true
% 11.78/2.01  --prep_def_merge_prop_impl              false
% 11.78/2.01  --prep_def_merge_mbd                    true
% 11.78/2.01  --prep_def_merge_tr_red                 false
% 11.78/2.01  --prep_def_merge_tr_cl                  false
% 11.78/2.01  --smt_preprocessing                     true
% 11.78/2.01  --smt_ac_axioms                         fast
% 11.78/2.01  --preprocessed_out                      false
% 11.78/2.01  --preprocessed_stats                    false
% 11.78/2.01  
% 11.78/2.01  ------ Abstraction refinement Options
% 11.78/2.01  
% 11.78/2.01  --abstr_ref                             []
% 11.78/2.01  --abstr_ref_prep                        false
% 11.78/2.01  --abstr_ref_until_sat                   false
% 11.78/2.01  --abstr_ref_sig_restrict                funpre
% 11.78/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.78/2.01  --abstr_ref_under                       []
% 11.78/2.01  
% 11.78/2.01  ------ SAT Options
% 11.78/2.01  
% 11.78/2.01  --sat_mode                              false
% 11.78/2.01  --sat_fm_restart_options                ""
% 11.78/2.01  --sat_gr_def                            false
% 11.78/2.01  --sat_epr_types                         true
% 11.78/2.01  --sat_non_cyclic_types                  false
% 11.78/2.01  --sat_finite_models                     false
% 11.78/2.01  --sat_fm_lemmas                         false
% 11.78/2.01  --sat_fm_prep                           false
% 11.78/2.01  --sat_fm_uc_incr                        true
% 11.78/2.01  --sat_out_model                         small
% 11.78/2.01  --sat_out_clauses                       false
% 11.78/2.01  
% 11.78/2.01  ------ QBF Options
% 11.78/2.01  
% 11.78/2.01  --qbf_mode                              false
% 11.78/2.01  --qbf_elim_univ                         false
% 11.78/2.01  --qbf_dom_inst                          none
% 11.78/2.01  --qbf_dom_pre_inst                      false
% 11.78/2.01  --qbf_sk_in                             false
% 11.78/2.01  --qbf_pred_elim                         true
% 11.78/2.01  --qbf_split                             512
% 11.78/2.01  
% 11.78/2.01  ------ BMC1 Options
% 11.78/2.01  
% 11.78/2.01  --bmc1_incremental                      false
% 11.78/2.01  --bmc1_axioms                           reachable_all
% 11.78/2.01  --bmc1_min_bound                        0
% 11.78/2.01  --bmc1_max_bound                        -1
% 11.78/2.01  --bmc1_max_bound_default                -1
% 11.78/2.01  --bmc1_symbol_reachability              true
% 11.78/2.01  --bmc1_property_lemmas                  false
% 11.78/2.01  --bmc1_k_induction                      false
% 11.78/2.01  --bmc1_non_equiv_states                 false
% 11.78/2.01  --bmc1_deadlock                         false
% 11.78/2.01  --bmc1_ucm                              false
% 11.78/2.01  --bmc1_add_unsat_core                   none
% 11.78/2.01  --bmc1_unsat_core_children              false
% 11.78/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.78/2.01  --bmc1_out_stat                         full
% 11.78/2.01  --bmc1_ground_init                      false
% 11.78/2.01  --bmc1_pre_inst_next_state              false
% 11.78/2.01  --bmc1_pre_inst_state                   false
% 11.78/2.01  --bmc1_pre_inst_reach_state             false
% 11.78/2.01  --bmc1_out_unsat_core                   false
% 11.78/2.01  --bmc1_aig_witness_out                  false
% 11.78/2.01  --bmc1_verbose                          false
% 11.78/2.01  --bmc1_dump_clauses_tptp                false
% 11.78/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.78/2.01  --bmc1_dump_file                        -
% 11.78/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.78/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.78/2.01  --bmc1_ucm_extend_mode                  1
% 11.78/2.01  --bmc1_ucm_init_mode                    2
% 11.78/2.01  --bmc1_ucm_cone_mode                    none
% 11.78/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.78/2.01  --bmc1_ucm_relax_model                  4
% 11.78/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.78/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.78/2.01  --bmc1_ucm_layered_model                none
% 11.78/2.01  --bmc1_ucm_max_lemma_size               10
% 11.78/2.01  
% 11.78/2.01  ------ AIG Options
% 11.78/2.01  
% 11.78/2.01  --aig_mode                              false
% 11.78/2.01  
% 11.78/2.01  ------ Instantiation Options
% 11.78/2.01  
% 11.78/2.01  --instantiation_flag                    true
% 11.78/2.01  --inst_sos_flag                         true
% 11.78/2.01  --inst_sos_phase                        true
% 11.78/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.78/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.78/2.01  --inst_lit_sel_side                     num_symb
% 11.78/2.01  --inst_solver_per_active                1400
% 11.78/2.01  --inst_solver_calls_frac                1.
% 11.78/2.01  --inst_passive_queue_type               priority_queues
% 11.78/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.78/2.01  --inst_passive_queues_freq              [25;2]
% 11.78/2.01  --inst_dismatching                      true
% 11.78/2.01  --inst_eager_unprocessed_to_passive     true
% 11.78/2.01  --inst_prop_sim_given                   true
% 11.78/2.01  --inst_prop_sim_new                     false
% 11.78/2.01  --inst_subs_new                         false
% 11.78/2.01  --inst_eq_res_simp                      false
% 11.78/2.01  --inst_subs_given                       false
% 11.78/2.01  --inst_orphan_elimination               true
% 11.78/2.01  --inst_learning_loop_flag               true
% 11.78/2.01  --inst_learning_start                   3000
% 11.78/2.01  --inst_learning_factor                  2
% 11.78/2.01  --inst_start_prop_sim_after_learn       3
% 11.78/2.01  --inst_sel_renew                        solver
% 11.78/2.01  --inst_lit_activity_flag                true
% 11.78/2.01  --inst_restr_to_given                   false
% 11.78/2.01  --inst_activity_threshold               500
% 11.78/2.01  --inst_out_proof                        true
% 11.78/2.01  
% 11.78/2.01  ------ Resolution Options
% 11.78/2.01  
% 11.78/2.01  --resolution_flag                       true
% 11.78/2.01  --res_lit_sel                           adaptive
% 11.78/2.01  --res_lit_sel_side                      none
% 11.78/2.01  --res_ordering                          kbo
% 11.78/2.01  --res_to_prop_solver                    active
% 11.78/2.01  --res_prop_simpl_new                    false
% 11.78/2.01  --res_prop_simpl_given                  true
% 11.78/2.01  --res_passive_queue_type                priority_queues
% 11.78/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.78/2.01  --res_passive_queues_freq               [15;5]
% 11.78/2.01  --res_forward_subs                      full
% 11.78/2.01  --res_backward_subs                     full
% 11.78/2.01  --res_forward_subs_resolution           true
% 11.78/2.01  --res_backward_subs_resolution          true
% 11.78/2.01  --res_orphan_elimination                true
% 11.78/2.01  --res_time_limit                        2.
% 11.78/2.01  --res_out_proof                         true
% 11.78/2.01  
% 11.78/2.01  ------ Superposition Options
% 11.78/2.01  
% 11.78/2.01  --superposition_flag                    true
% 11.78/2.01  --sup_passive_queue_type                priority_queues
% 11.78/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.78/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.78/2.01  --demod_completeness_check              fast
% 11.78/2.01  --demod_use_ground                      true
% 11.78/2.01  --sup_to_prop_solver                    passive
% 11.78/2.01  --sup_prop_simpl_new                    true
% 11.78/2.01  --sup_prop_simpl_given                  true
% 11.78/2.01  --sup_fun_splitting                     true
% 11.78/2.01  --sup_smt_interval                      50000
% 11.78/2.01  
% 11.78/2.01  ------ Superposition Simplification Setup
% 11.78/2.01  
% 11.78/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.78/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.78/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.78/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.78/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.78/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.78/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.78/2.01  --sup_immed_triv                        [TrivRules]
% 11.78/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/2.01  --sup_immed_bw_main                     []
% 11.78/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.78/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.78/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/2.01  --sup_input_bw                          []
% 11.78/2.01  
% 11.78/2.01  ------ Combination Options
% 11.78/2.01  
% 11.78/2.01  --comb_res_mult                         3
% 11.78/2.01  --comb_sup_mult                         2
% 11.78/2.01  --comb_inst_mult                        10
% 11.78/2.01  
% 11.78/2.01  ------ Debug Options
% 11.78/2.01  
% 11.78/2.01  --dbg_backtrace                         false
% 11.78/2.01  --dbg_dump_prop_clauses                 false
% 11.78/2.01  --dbg_dump_prop_clauses_file            -
% 11.78/2.01  --dbg_out_stat                          false
% 11.78/2.01  ------ Parsing...
% 11.78/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/2.01  ------ Proving...
% 11.78/2.01  ------ Problem Properties 
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  clauses                                 20
% 11.78/2.01  conjectures                             2
% 11.78/2.01  EPR                                     3
% 11.78/2.01  Horn                                    17
% 11.78/2.01  unary                                   9
% 11.78/2.01  binary                                  4
% 11.78/2.01  lits                                    41
% 11.78/2.01  lits eq                                 18
% 11.78/2.01  fd_pure                                 0
% 11.78/2.01  fd_pseudo                               0
% 11.78/2.01  fd_cond                                 0
% 11.78/2.01  fd_pseudo_cond                          5
% 11.78/2.01  AC symbols                              0
% 11.78/2.01  
% 11.78/2.01  ------ Schedule dynamic 5 is on 
% 11.78/2.01  
% 11.78/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  ------ 
% 11.78/2.01  Current options:
% 11.78/2.01  ------ 
% 11.78/2.01  
% 11.78/2.01  ------ Input Options
% 11.78/2.01  
% 11.78/2.01  --out_options                           all
% 11.78/2.01  --tptp_safe_out                         true
% 11.78/2.01  --problem_path                          ""
% 11.78/2.01  --include_path                          ""
% 11.78/2.01  --clausifier                            res/vclausify_rel
% 11.78/2.01  --clausifier_options                    ""
% 11.78/2.01  --stdin                                 false
% 11.78/2.01  --stats_out                             all
% 11.78/2.01  
% 11.78/2.01  ------ General Options
% 11.78/2.01  
% 11.78/2.01  --fof                                   false
% 11.78/2.01  --time_out_real                         305.
% 11.78/2.01  --time_out_virtual                      -1.
% 11.78/2.01  --symbol_type_check                     false
% 11.78/2.01  --clausify_out                          false
% 11.78/2.01  --sig_cnt_out                           false
% 11.78/2.01  --trig_cnt_out                          false
% 11.78/2.01  --trig_cnt_out_tolerance                1.
% 11.78/2.01  --trig_cnt_out_sk_spl                   false
% 11.78/2.01  --abstr_cl_out                          false
% 11.78/2.01  
% 11.78/2.01  ------ Global Options
% 11.78/2.01  
% 11.78/2.01  --schedule                              default
% 11.78/2.01  --add_important_lit                     false
% 11.78/2.01  --prop_solver_per_cl                    1000
% 11.78/2.01  --min_unsat_core                        false
% 11.78/2.01  --soft_assumptions                      false
% 11.78/2.01  --soft_lemma_size                       3
% 11.78/2.01  --prop_impl_unit_size                   0
% 11.78/2.01  --prop_impl_unit                        []
% 11.78/2.01  --share_sel_clauses                     true
% 11.78/2.01  --reset_solvers                         false
% 11.78/2.01  --bc_imp_inh                            [conj_cone]
% 11.78/2.01  --conj_cone_tolerance                   3.
% 11.78/2.01  --extra_neg_conj                        none
% 11.78/2.01  --large_theory_mode                     true
% 11.78/2.01  --prolific_symb_bound                   200
% 11.78/2.01  --lt_threshold                          2000
% 11.78/2.01  --clause_weak_htbl                      true
% 11.78/2.01  --gc_record_bc_elim                     false
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing Options
% 11.78/2.01  
% 11.78/2.01  --preprocessing_flag                    true
% 11.78/2.01  --time_out_prep_mult                    0.1
% 11.78/2.01  --splitting_mode                        input
% 11.78/2.01  --splitting_grd                         true
% 11.78/2.01  --splitting_cvd                         false
% 11.78/2.01  --splitting_cvd_svl                     false
% 11.78/2.01  --splitting_nvd                         32
% 11.78/2.01  --sub_typing                            true
% 11.78/2.01  --prep_gs_sim                           true
% 11.78/2.01  --prep_unflatten                        true
% 11.78/2.01  --prep_res_sim                          true
% 11.78/2.01  --prep_upred                            true
% 11.78/2.01  --prep_sem_filter                       exhaustive
% 11.78/2.01  --prep_sem_filter_out                   false
% 11.78/2.01  --pred_elim                             true
% 11.78/2.01  --res_sim_input                         true
% 11.78/2.01  --eq_ax_congr_red                       true
% 11.78/2.01  --pure_diseq_elim                       true
% 11.78/2.01  --brand_transform                       false
% 11.78/2.01  --non_eq_to_eq                          false
% 11.78/2.01  --prep_def_merge                        true
% 11.78/2.01  --prep_def_merge_prop_impl              false
% 11.78/2.01  --prep_def_merge_mbd                    true
% 11.78/2.01  --prep_def_merge_tr_red                 false
% 11.78/2.01  --prep_def_merge_tr_cl                  false
% 11.78/2.01  --smt_preprocessing                     true
% 11.78/2.01  --smt_ac_axioms                         fast
% 11.78/2.01  --preprocessed_out                      false
% 11.78/2.01  --preprocessed_stats                    false
% 11.78/2.01  
% 11.78/2.01  ------ Abstraction refinement Options
% 11.78/2.01  
% 11.78/2.01  --abstr_ref                             []
% 11.78/2.01  --abstr_ref_prep                        false
% 11.78/2.01  --abstr_ref_until_sat                   false
% 11.78/2.01  --abstr_ref_sig_restrict                funpre
% 11.78/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.78/2.01  --abstr_ref_under                       []
% 11.78/2.01  
% 11.78/2.01  ------ SAT Options
% 11.78/2.01  
% 11.78/2.01  --sat_mode                              false
% 11.78/2.01  --sat_fm_restart_options                ""
% 11.78/2.01  --sat_gr_def                            false
% 11.78/2.01  --sat_epr_types                         true
% 11.78/2.01  --sat_non_cyclic_types                  false
% 11.78/2.01  --sat_finite_models                     false
% 11.78/2.01  --sat_fm_lemmas                         false
% 11.78/2.01  --sat_fm_prep                           false
% 11.78/2.01  --sat_fm_uc_incr                        true
% 11.78/2.01  --sat_out_model                         small
% 11.78/2.01  --sat_out_clauses                       false
% 11.78/2.01  
% 11.78/2.01  ------ QBF Options
% 11.78/2.01  
% 11.78/2.01  --qbf_mode                              false
% 11.78/2.01  --qbf_elim_univ                         false
% 11.78/2.01  --qbf_dom_inst                          none
% 11.78/2.01  --qbf_dom_pre_inst                      false
% 11.78/2.01  --qbf_sk_in                             false
% 11.78/2.01  --qbf_pred_elim                         true
% 11.78/2.01  --qbf_split                             512
% 11.78/2.01  
% 11.78/2.01  ------ BMC1 Options
% 11.78/2.01  
% 11.78/2.01  --bmc1_incremental                      false
% 11.78/2.01  --bmc1_axioms                           reachable_all
% 11.78/2.01  --bmc1_min_bound                        0
% 11.78/2.01  --bmc1_max_bound                        -1
% 11.78/2.01  --bmc1_max_bound_default                -1
% 11.78/2.01  --bmc1_symbol_reachability              true
% 11.78/2.01  --bmc1_property_lemmas                  false
% 11.78/2.01  --bmc1_k_induction                      false
% 11.78/2.01  --bmc1_non_equiv_states                 false
% 11.78/2.01  --bmc1_deadlock                         false
% 11.78/2.01  --bmc1_ucm                              false
% 11.78/2.01  --bmc1_add_unsat_core                   none
% 11.78/2.01  --bmc1_unsat_core_children              false
% 11.78/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.78/2.01  --bmc1_out_stat                         full
% 11.78/2.01  --bmc1_ground_init                      false
% 11.78/2.01  --bmc1_pre_inst_next_state              false
% 11.78/2.01  --bmc1_pre_inst_state                   false
% 11.78/2.01  --bmc1_pre_inst_reach_state             false
% 11.78/2.01  --bmc1_out_unsat_core                   false
% 11.78/2.01  --bmc1_aig_witness_out                  false
% 11.78/2.01  --bmc1_verbose                          false
% 11.78/2.01  --bmc1_dump_clauses_tptp                false
% 11.78/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.78/2.01  --bmc1_dump_file                        -
% 11.78/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.78/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.78/2.01  --bmc1_ucm_extend_mode                  1
% 11.78/2.01  --bmc1_ucm_init_mode                    2
% 11.78/2.01  --bmc1_ucm_cone_mode                    none
% 11.78/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.78/2.01  --bmc1_ucm_relax_model                  4
% 11.78/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.78/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.78/2.01  --bmc1_ucm_layered_model                none
% 11.78/2.01  --bmc1_ucm_max_lemma_size               10
% 11.78/2.01  
% 11.78/2.01  ------ AIG Options
% 11.78/2.01  
% 11.78/2.01  --aig_mode                              false
% 11.78/2.01  
% 11.78/2.01  ------ Instantiation Options
% 11.78/2.01  
% 11.78/2.01  --instantiation_flag                    true
% 11.78/2.01  --inst_sos_flag                         true
% 11.78/2.01  --inst_sos_phase                        true
% 11.78/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.78/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.78/2.01  --inst_lit_sel_side                     none
% 11.78/2.01  --inst_solver_per_active                1400
% 11.78/2.01  --inst_solver_calls_frac                1.
% 11.78/2.01  --inst_passive_queue_type               priority_queues
% 11.78/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.78/2.01  --inst_passive_queues_freq              [25;2]
% 11.78/2.01  --inst_dismatching                      true
% 11.78/2.01  --inst_eager_unprocessed_to_passive     true
% 11.78/2.01  --inst_prop_sim_given                   true
% 11.78/2.01  --inst_prop_sim_new                     false
% 11.78/2.01  --inst_subs_new                         false
% 11.78/2.01  --inst_eq_res_simp                      false
% 11.78/2.01  --inst_subs_given                       false
% 11.78/2.01  --inst_orphan_elimination               true
% 11.78/2.01  --inst_learning_loop_flag               true
% 11.78/2.01  --inst_learning_start                   3000
% 11.78/2.01  --inst_learning_factor                  2
% 11.78/2.01  --inst_start_prop_sim_after_learn       3
% 11.78/2.01  --inst_sel_renew                        solver
% 11.78/2.01  --inst_lit_activity_flag                true
% 11.78/2.01  --inst_restr_to_given                   false
% 11.78/2.01  --inst_activity_threshold               500
% 11.78/2.01  --inst_out_proof                        true
% 11.78/2.01  
% 11.78/2.01  ------ Resolution Options
% 11.78/2.01  
% 11.78/2.01  --resolution_flag                       false
% 11.78/2.01  --res_lit_sel                           adaptive
% 11.78/2.01  --res_lit_sel_side                      none
% 11.78/2.01  --res_ordering                          kbo
% 11.78/2.01  --res_to_prop_solver                    active
% 11.78/2.01  --res_prop_simpl_new                    false
% 11.78/2.01  --res_prop_simpl_given                  true
% 11.78/2.01  --res_passive_queue_type                priority_queues
% 11.78/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.78/2.01  --res_passive_queues_freq               [15;5]
% 11.78/2.01  --res_forward_subs                      full
% 11.78/2.01  --res_backward_subs                     full
% 11.78/2.01  --res_forward_subs_resolution           true
% 11.78/2.01  --res_backward_subs_resolution          true
% 11.78/2.01  --res_orphan_elimination                true
% 11.78/2.01  --res_time_limit                        2.
% 11.78/2.01  --res_out_proof                         true
% 11.78/2.01  
% 11.78/2.01  ------ Superposition Options
% 11.78/2.01  
% 11.78/2.01  --superposition_flag                    true
% 11.78/2.01  --sup_passive_queue_type                priority_queues
% 11.78/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.78/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.78/2.01  --demod_completeness_check              fast
% 11.78/2.01  --demod_use_ground                      true
% 11.78/2.01  --sup_to_prop_solver                    passive
% 11.78/2.01  --sup_prop_simpl_new                    true
% 11.78/2.01  --sup_prop_simpl_given                  true
% 11.78/2.01  --sup_fun_splitting                     true
% 11.78/2.01  --sup_smt_interval                      50000
% 11.78/2.01  
% 11.78/2.01  ------ Superposition Simplification Setup
% 11.78/2.01  
% 11.78/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.78/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.78/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.78/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.78/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.78/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.78/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.78/2.01  --sup_immed_triv                        [TrivRules]
% 11.78/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/2.01  --sup_immed_bw_main                     []
% 11.78/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.78/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.78/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/2.01  --sup_input_bw                          []
% 11.78/2.01  
% 11.78/2.01  ------ Combination Options
% 11.78/2.01  
% 11.78/2.01  --comb_res_mult                         3
% 11.78/2.01  --comb_sup_mult                         2
% 11.78/2.01  --comb_inst_mult                        10
% 11.78/2.01  
% 11.78/2.01  ------ Debug Options
% 11.78/2.01  
% 11.78/2.01  --dbg_backtrace                         false
% 11.78/2.01  --dbg_dump_prop_clauses                 false
% 11.78/2.01  --dbg_dump_prop_clauses_file            -
% 11.78/2.01  --dbg_out_stat                          false
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  ------ Proving...
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  % SZS status Theorem for theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  fof(f8,axiom,(
% 11.78/2.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f46,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f8])).
% 11.78/2.01  
% 11.78/2.01  fof(f6,axiom,(
% 11.78/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f44,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 11.78/2.01    inference(cnf_transformation,[],[f6])).
% 11.78/2.01  
% 11.78/2.01  fof(f12,axiom,(
% 11.78/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f50,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.78/2.01    inference(cnf_transformation,[],[f12])).
% 11.78/2.01  
% 11.78/2.01  fof(f7,axiom,(
% 11.78/2.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f45,plain,(
% 11.78/2.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f7])).
% 11.78/2.01  
% 11.78/2.01  fof(f56,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 11.78/2.01    inference(definition_unfolding,[],[f44,f50,f45])).
% 11.78/2.01  
% 11.78/2.01  fof(f58,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 11.78/2.01    inference(definition_unfolding,[],[f46,f56])).
% 11.78/2.01  
% 11.78/2.01  fof(f3,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f20,plain,(
% 11.78/2.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.78/2.01    inference(ennf_transformation,[],[f3])).
% 11.78/2.01  
% 11.78/2.01  fof(f23,plain,(
% 11.78/2.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/2.01    inference(nnf_transformation,[],[f20])).
% 11.78/2.01  
% 11.78/2.01  fof(f24,plain,(
% 11.78/2.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/2.01    inference(flattening,[],[f23])).
% 11.78/2.01  
% 11.78/2.01  fof(f25,plain,(
% 11.78/2.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/2.01    inference(rectify,[],[f24])).
% 11.78/2.01  
% 11.78/2.01  fof(f26,plain,(
% 11.78/2.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 11.78/2.01    introduced(choice_axiom,[])).
% 11.78/2.01  
% 11.78/2.01  fof(f27,plain,(
% 11.78/2.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 11.78/2.01  
% 11.78/2.01  fof(f35,plain,(
% 11.78/2.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.78/2.01    inference(cnf_transformation,[],[f27])).
% 11.78/2.01  
% 11.78/2.01  fof(f65,plain,(
% 11.78/2.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) != X3) )),
% 11.78/2.01    inference(definition_unfolding,[],[f35,f56])).
% 11.78/2.01  
% 11.78/2.01  fof(f75,plain,(
% 11.78/2.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2))) != X3) )),
% 11.78/2.01    inference(equality_resolution,[],[f65])).
% 11.78/2.01  
% 11.78/2.01  fof(f76,plain,(
% 11.78/2.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2))))) )),
% 11.78/2.01    inference(equality_resolution,[],[f75])).
% 11.78/2.01  
% 11.78/2.01  fof(f11,axiom,(
% 11.78/2.01    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f21,plain,(
% 11.78/2.01    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 11.78/2.01    inference(ennf_transformation,[],[f11])).
% 11.78/2.01  
% 11.78/2.01  fof(f49,plain,(
% 11.78/2.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f21])).
% 11.78/2.01  
% 11.78/2.01  fof(f2,axiom,(
% 11.78/2.01    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f16,plain,(
% 11.78/2.01    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 11.78/2.01    inference(unused_predicate_definition_removal,[],[f2])).
% 11.78/2.01  
% 11.78/2.01  fof(f18,plain,(
% 11.78/2.01    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 11.78/2.01    inference(ennf_transformation,[],[f16])).
% 11.78/2.01  
% 11.78/2.01  fof(f19,plain,(
% 11.78/2.01    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 11.78/2.01    inference(flattening,[],[f18])).
% 11.78/2.01  
% 11.78/2.01  fof(f33,plain,(
% 11.78/2.01    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f19])).
% 11.78/2.01  
% 11.78/2.01  fof(f5,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f43,plain,(
% 11.78/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f5])).
% 11.78/2.01  
% 11.78/2.01  fof(f4,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f42,plain,(
% 11.78/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 11.78/2.01    inference(cnf_transformation,[],[f4])).
% 11.78/2.01  
% 11.78/2.01  fof(f57,plain,(
% 11.78/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))) )),
% 11.78/2.01    inference(definition_unfolding,[],[f42,f50])).
% 11.78/2.01  
% 11.78/2.01  fof(f67,plain,(
% 11.78/2.01    ( ! [X2,X0,X3,X1] : (k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X3,X2),k2_tarski(X1,X0)))) )),
% 11.78/2.01    inference(definition_unfolding,[],[f43,f57,f57])).
% 11.78/2.01  
% 11.78/2.01  fof(f14,conjecture,(
% 11.78/2.01    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f15,negated_conjecture,(
% 11.78/2.01    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 11.78/2.01    inference(negated_conjecture,[],[f14])).
% 11.78/2.01  
% 11.78/2.01  fof(f22,plain,(
% 11.78/2.01    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 11.78/2.01    inference(ennf_transformation,[],[f15])).
% 11.78/2.01  
% 11.78/2.01  fof(f30,plain,(
% 11.78/2.01    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK1,sK2) & r1_tarski(k2_xboole_0(k1_tarski(sK1),sK2),sK2))),
% 11.78/2.01    introduced(choice_axiom,[])).
% 11.78/2.01  
% 11.78/2.01  fof(f31,plain,(
% 11.78/2.01    ~r2_hidden(sK1,sK2) & r1_tarski(k2_xboole_0(k1_tarski(sK1),sK2),sK2)),
% 11.78/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f30])).
% 11.78/2.01  
% 11.78/2.01  fof(f54,plain,(
% 11.78/2.01    r1_tarski(k2_xboole_0(k1_tarski(sK1),sK2),sK2)),
% 11.78/2.01    inference(cnf_transformation,[],[f31])).
% 11.78/2.01  
% 11.78/2.01  fof(f70,plain,(
% 11.78/2.01    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK2)),sK2)),
% 11.78/2.01    inference(definition_unfolding,[],[f54,f50,f45])).
% 11.78/2.01  
% 11.78/2.01  fof(f1,axiom,(
% 11.78/2.01    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f17,plain,(
% 11.78/2.01    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 11.78/2.01    inference(ennf_transformation,[],[f1])).
% 11.78/2.01  
% 11.78/2.01  fof(f32,plain,(
% 11.78/2.01    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f17])).
% 11.78/2.01  
% 11.78/2.01  fof(f37,plain,(
% 11.78/2.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.78/2.01    inference(cnf_transformation,[],[f27])).
% 11.78/2.01  
% 11.78/2.01  fof(f63,plain,(
% 11.78/2.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) != X3) )),
% 11.78/2.01    inference(definition_unfolding,[],[f37,f56])).
% 11.78/2.01  
% 11.78/2.01  fof(f71,plain,(
% 11.78/2.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X5,X5))) != X3) )),
% 11.78/2.01    inference(equality_resolution,[],[f63])).
% 11.78/2.01  
% 11.78/2.01  fof(f72,plain,(
% 11.78/2.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X5,X5))))) )),
% 11.78/2.01    inference(equality_resolution,[],[f71])).
% 11.78/2.01  
% 11.78/2.01  fof(f13,axiom,(
% 11.78/2.01    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f28,plain,(
% 11.78/2.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.78/2.01    inference(nnf_transformation,[],[f13])).
% 11.78/2.01  
% 11.78/2.01  fof(f29,plain,(
% 11.78/2.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.78/2.01    inference(flattening,[],[f28])).
% 11.78/2.01  
% 11.78/2.01  fof(f52,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f29])).
% 11.78/2.01  
% 11.78/2.01  fof(f55,plain,(
% 11.78/2.01    ~r2_hidden(sK1,sK2)),
% 11.78/2.01    inference(cnf_transformation,[],[f31])).
% 11.78/2.01  
% 11.78/2.01  cnf(c_0,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 11.78/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_9,plain,
% 11.78/2.01      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) ),
% 11.78/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_567,plain,
% 11.78/2.01      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_765,plain,
% 11.78/2.01      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_0,c_567]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_14,plain,
% 11.78/2.01      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 11.78/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_565,plain,
% 11.78/2.01      ( r2_hidden(X0,X1) != iProver_top
% 11.78/2.01      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_2,plain,
% 11.78/2.01      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 11.78/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_574,plain,
% 11.78/2.01      ( X0 = X1
% 11.78/2.01      | r1_tarski(X1,X0) != iProver_top
% 11.78/2.01      | r2_xboole_0(X1,X0) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_9187,plain,
% 11.78/2.01      ( k3_tarski(X0) = X1
% 11.78/2.01      | r2_hidden(X1,X0) != iProver_top
% 11.78/2.01      | r2_xboole_0(X1,k3_tarski(X0)) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_565,c_574]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_11,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X3,X2),k2_tarski(X1,X0))) ),
% 11.78/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1060,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X1,X0) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1502,plain,
% 11.78/2.01      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_1060,c_0]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_19,negated_conjecture,
% 11.78/2.01      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK2)),sK2) ),
% 11.78/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_560,plain,
% 11.78/2.01      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK2)),sK2) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1579,plain,
% 11.78/2.01      ( r1_tarski(k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))),sK2) = iProver_top ),
% 11.78/2.01      inference(demodulation,[status(thm)],[c_1502,c_560]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_9189,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2
% 11.78/2.01      | r2_xboole_0(k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))),sK2) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_1579,c_574]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1,plain,
% 11.78/2.01      ( ~ r2_xboole_0(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 11.78/2.01      inference(cnf_transformation,[],[f32]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_575,plain,
% 11.78/2.01      ( r2_xboole_0(X0,X1) != iProver_top
% 11.78/2.01      | r2_xboole_0(X1,X0) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_9668,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2
% 11.78/2.01      | r2_xboole_0(sK2,k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1)))) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_9189,c_575]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_49882,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2
% 11.78/2.01      | r2_hidden(sK2,k2_tarski(sK2,k2_tarski(sK1,sK1))) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_9187,c_9668]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_50030,plain,
% 11.78/2.01      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK1,sK1))) = sK2 ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_765,c_49882]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_7,plain,
% 11.78/2.01      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
% 11.78/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_569,plain,
% 11.78/2.01      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_933,plain,
% 11.78/2.01      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_0,c_569]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_16,plain,
% 11.78/2.01      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
% 11.78/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_563,plain,
% 11.78/2.01      ( r2_hidden(X0,X1) = iProver_top
% 11.78/2.01      | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3131,plain,
% 11.78/2.01      ( r2_hidden(X0,k3_tarski(X1)) = iProver_top
% 11.78/2.01      | r2_hidden(k2_tarski(X2,X0),X1) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_565,c_563]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_12208,plain,
% 11.78/2.01      ( r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X2,X0)))) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_933,c_3131]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_50035,plain,
% 11.78/2.01      ( r2_hidden(sK1,sK2) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_50030,c_12208]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_18,negated_conjecture,
% 11.78/2.01      ( ~ r2_hidden(sK1,sK2) ),
% 11.78/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_21,plain,
% 11.78/2.01      ( r2_hidden(sK1,sK2) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(contradiction,plain,
% 11.78/2.01      ( $false ),
% 11.78/2.01      inference(minisat,[status(thm)],[c_50035,c_21]) ).
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  ------                               Statistics
% 11.78/2.01  
% 11.78/2.01  ------ General
% 11.78/2.01  
% 11.78/2.01  abstr_ref_over_cycles:                  0
% 11.78/2.01  abstr_ref_under_cycles:                 0
% 11.78/2.01  gc_basic_clause_elim:                   0
% 11.78/2.01  forced_gc_time:                         0
% 11.78/2.01  parsing_time:                           0.008
% 11.78/2.01  unif_index_cands_time:                  0.
% 11.78/2.01  unif_index_add_time:                    0.
% 11.78/2.01  orderings_time:                         0.
% 11.78/2.01  out_proof_time:                         0.008
% 11.78/2.01  total_time:                             1.33
% 11.78/2.01  num_of_symbols:                         40
% 11.78/2.01  num_of_terms:                           38434
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing
% 11.78/2.01  
% 11.78/2.01  num_of_splits:                          0
% 11.78/2.01  num_of_split_atoms:                     0
% 11.78/2.01  num_of_reused_defs:                     0
% 11.78/2.01  num_eq_ax_congr_red:                    22
% 11.78/2.01  num_of_sem_filtered_clauses:            1
% 11.78/2.01  num_of_subtypes:                        0
% 11.78/2.01  monotx_restored_types:                  0
% 11.78/2.01  sat_num_of_epr_types:                   0
% 11.78/2.01  sat_num_of_non_cyclic_types:            0
% 11.78/2.01  sat_guarded_non_collapsed_types:        0
% 11.78/2.01  num_pure_diseq_elim:                    0
% 11.78/2.01  simp_replaced_by:                       0
% 11.78/2.01  res_preprocessed:                       73
% 11.78/2.01  prep_upred:                             0
% 11.78/2.01  prep_unflattend:                        13
% 11.78/2.01  smt_new_axioms:                         0
% 11.78/2.01  pred_elim_cands:                        3
% 11.78/2.01  pred_elim:                              0
% 11.78/2.01  pred_elim_cl:                           0
% 11.78/2.01  pred_elim_cycles:                       1
% 11.78/2.01  merged_defs:                            0
% 11.78/2.01  merged_defs_ncl:                        0
% 11.78/2.01  bin_hyper_res:                          0
% 11.78/2.01  prep_cycles:                            3
% 11.78/2.01  pred_elim_time:                         0.002
% 11.78/2.01  splitting_time:                         0.
% 11.78/2.01  sem_filter_time:                        0.
% 11.78/2.01  monotx_time:                            0.
% 11.78/2.01  subtype_inf_time:                       0.
% 11.78/2.01  
% 11.78/2.01  ------ Problem properties
% 11.78/2.01  
% 11.78/2.01  clauses:                                20
% 11.78/2.01  conjectures:                            2
% 11.78/2.01  epr:                                    3
% 11.78/2.01  horn:                                   17
% 11.78/2.01  ground:                                 2
% 11.78/2.01  unary:                                  9
% 11.78/2.01  binary:                                 4
% 11.78/2.01  lits:                                   41
% 11.78/2.01  lits_eq:                                18
% 11.78/2.01  fd_pure:                                0
% 11.78/2.01  fd_pseudo:                              0
% 11.78/2.01  fd_cond:                                0
% 11.78/2.01  fd_pseudo_cond:                         5
% 11.78/2.01  ac_symbols:                             0
% 11.78/2.01  
% 11.78/2.01  ------ Propositional Solver
% 11.78/2.01  
% 11.78/2.01  prop_solver_calls:                      29
% 11.78/2.01  prop_fast_solver_calls:                 696
% 11.78/2.01  smt_solver_calls:                       0
% 11.78/2.01  smt_fast_solver_calls:                  0
% 11.78/2.01  prop_num_of_clauses:                    9681
% 11.78/2.01  prop_preprocess_simplified:             23098
% 11.78/2.01  prop_fo_subsumed:                       0
% 11.78/2.01  prop_solver_time:                       0.
% 11.78/2.01  smt_solver_time:                        0.
% 11.78/2.01  smt_fast_solver_time:                   0.
% 11.78/2.01  prop_fast_solver_time:                  0.
% 11.78/2.01  prop_unsat_core_time:                   0.001
% 11.78/2.01  
% 11.78/2.01  ------ QBF
% 11.78/2.01  
% 11.78/2.01  qbf_q_res:                              0
% 11.78/2.01  qbf_num_tautologies:                    0
% 11.78/2.01  qbf_prep_cycles:                        0
% 11.78/2.01  
% 11.78/2.01  ------ BMC1
% 11.78/2.01  
% 11.78/2.01  bmc1_current_bound:                     -1
% 11.78/2.01  bmc1_last_solved_bound:                 -1
% 11.78/2.01  bmc1_unsat_core_size:                   -1
% 11.78/2.01  bmc1_unsat_core_parents_size:           -1
% 11.78/2.01  bmc1_merge_next_fun:                    0
% 11.78/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.78/2.01  
% 11.78/2.01  ------ Instantiation
% 11.78/2.01  
% 11.78/2.01  inst_num_of_clauses:                    2657
% 11.78/2.01  inst_num_in_passive:                    1351
% 11.78/2.01  inst_num_in_active:                     1122
% 11.78/2.01  inst_num_in_unprocessed:                184
% 11.78/2.01  inst_num_of_loops:                      1270
% 11.78/2.01  inst_num_of_learning_restarts:          0
% 11.78/2.01  inst_num_moves_active_passive:          143
% 11.78/2.01  inst_lit_activity:                      0
% 11.78/2.01  inst_lit_activity_moves:                0
% 11.78/2.01  inst_num_tautologies:                   0
% 11.78/2.01  inst_num_prop_implied:                  0
% 11.78/2.01  inst_num_existing_simplified:           0
% 11.78/2.01  inst_num_eq_res_simplified:             0
% 11.78/2.01  inst_num_child_elim:                    0
% 11.78/2.01  inst_num_of_dismatching_blockings:      6043
% 11.78/2.01  inst_num_of_non_proper_insts:           4390
% 11.78/2.01  inst_num_of_duplicates:                 0
% 11.78/2.01  inst_inst_num_from_inst_to_res:         0
% 11.78/2.01  inst_dismatching_checking_time:         0.
% 11.78/2.01  
% 11.78/2.01  ------ Resolution
% 11.78/2.01  
% 11.78/2.01  res_num_of_clauses:                     0
% 11.78/2.01  res_num_in_passive:                     0
% 11.78/2.01  res_num_in_active:                      0
% 11.78/2.01  res_num_of_loops:                       76
% 11.78/2.01  res_forward_subset_subsumed:            1664
% 11.78/2.01  res_backward_subset_subsumed:           0
% 11.78/2.01  res_forward_subsumed:                   0
% 11.78/2.01  res_backward_subsumed:                  0
% 11.78/2.01  res_forward_subsumption_resolution:     0
% 11.78/2.01  res_backward_subsumption_resolution:    0
% 11.78/2.01  res_clause_to_clause_subsumption:       8136
% 11.78/2.01  res_orphan_elimination:                 0
% 11.78/2.01  res_tautology_del:                      902
% 11.78/2.01  res_num_eq_res_simplified:              0
% 11.78/2.01  res_num_sel_changes:                    0
% 11.78/2.01  res_moves_from_active_to_pass:          0
% 11.78/2.01  
% 11.78/2.01  ------ Superposition
% 11.78/2.01  
% 11.78/2.01  sup_time_total:                         0.
% 11.78/2.01  sup_time_generating:                    0.
% 11.78/2.01  sup_time_sim_full:                      0.
% 11.78/2.01  sup_time_sim_immed:                     0.
% 11.78/2.01  
% 11.78/2.01  sup_num_of_clauses:                     554
% 11.78/2.01  sup_num_in_active:                      220
% 11.78/2.01  sup_num_in_passive:                     334
% 11.78/2.01  sup_num_of_loops:                       253
% 11.78/2.01  sup_fw_superposition:                   12505
% 11.78/2.01  sup_bw_superposition:                   7360
% 11.78/2.01  sup_immediate_simplified:               182
% 11.78/2.01  sup_given_eliminated:                   0
% 11.78/2.01  comparisons_done:                       0
% 11.78/2.01  comparisons_avoided:                    6
% 11.78/2.01  
% 11.78/2.01  ------ Simplifications
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  sim_fw_subset_subsumed:                 1
% 11.78/2.01  sim_bw_subset_subsumed:                 4
% 11.78/2.01  sim_fw_subsumed:                        117
% 11.78/2.01  sim_bw_subsumed:                        29
% 11.78/2.01  sim_fw_subsumption_res:                 0
% 11.78/2.01  sim_bw_subsumption_res:                 0
% 11.78/2.01  sim_tautology_del:                      2
% 11.78/2.01  sim_eq_tautology_del:                   26
% 11.78/2.01  sim_eq_res_simp:                        0
% 11.78/2.01  sim_fw_demodulated:                     59
% 11.78/2.01  sim_bw_demodulated:                     3
% 11.78/2.01  sim_light_normalised:                   49
% 11.78/2.01  sim_joinable_taut:                      0
% 11.78/2.01  sim_joinable_simp:                      0
% 11.78/2.01  sim_ac_normalised:                      0
% 11.78/2.01  sim_smt_subsumption:                    0
% 11.78/2.01  
%------------------------------------------------------------------------------
