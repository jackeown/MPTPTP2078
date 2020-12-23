%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:08 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 204 expanded)
%              Number of clauses        :   34 (  47 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  279 ( 428 expanded)
%              Number of equality atoms :  194 ( 321 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f86,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK2 = sK3
        | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) )
      & ( sK2 != sK3
        | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( sK2 = sK3
      | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) )
    & ( sK2 != sK3
      | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).

fof(f56,plain,
    ( sK2 = sK3
    | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,
    ( sK2 = sK3
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f56,f34,f58,f58,f58])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f55,plain,
    ( sK2 != sK3
    | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( sK2 != sK3
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f55,f34,f58,f58,f58])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f77,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f78,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f77])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f53,f58])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1425,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1441,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1751,plain,
    ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_1441])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1427,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3003,plain,
    ( X0 = X1
    | k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1751,c_1427])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) != k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 = sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3025,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) != k2_enumset1(sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3003,c_19])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1440,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1749,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1440,c_1441])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2014,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1749,c_2])).

cnf(c_3028,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != k2_enumset1(sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_3025,c_2014])).

cnf(c_3029,plain,
    ( sK3 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_3028])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3120,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_3029,c_20])).

cnf(c_3122,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_3120])).

cnf(c_4,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1439,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1750,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1439,c_1441])).

cnf(c_4067,plain,
    ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3122,c_1750])).

cnf(c_4086,plain,
    ( r1_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_1439])).

cnf(c_4088,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4086,c_2014])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_655,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | X0 != X2
    | k2_enumset1(X3,X3,X4,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_145])).

cnf(c_656,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_657,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_659,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4088,c_659])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:24:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.33/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.95  
% 2.33/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.95  
% 2.33/0.95  ------  iProver source info
% 2.33/0.95  
% 2.33/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.95  git: non_committed_changes: false
% 2.33/0.95  git: last_make_outside_of_git: false
% 2.33/0.95  
% 2.33/0.95  ------ 
% 2.33/0.95  
% 2.33/0.95  ------ Input Options
% 2.33/0.95  
% 2.33/0.95  --out_options                           all
% 2.33/0.95  --tptp_safe_out                         true
% 2.33/0.95  --problem_path                          ""
% 2.33/0.95  --include_path                          ""
% 2.33/0.95  --clausifier                            res/vclausify_rel
% 2.33/0.95  --clausifier_options                    --mode clausify
% 2.33/0.95  --stdin                                 false
% 2.33/0.95  --stats_out                             all
% 2.33/0.95  
% 2.33/0.95  ------ General Options
% 2.33/0.95  
% 2.33/0.95  --fof                                   false
% 2.33/0.95  --time_out_real                         305.
% 2.33/0.95  --time_out_virtual                      -1.
% 2.33/0.95  --symbol_type_check                     false
% 2.33/0.95  --clausify_out                          false
% 2.33/0.95  --sig_cnt_out                           false
% 2.33/0.95  --trig_cnt_out                          false
% 2.33/0.95  --trig_cnt_out_tolerance                1.
% 2.33/0.95  --trig_cnt_out_sk_spl                   false
% 2.33/0.95  --abstr_cl_out                          false
% 2.33/0.95  
% 2.33/0.95  ------ Global Options
% 2.33/0.95  
% 2.33/0.95  --schedule                              default
% 2.33/0.95  --add_important_lit                     false
% 2.33/0.95  --prop_solver_per_cl                    1000
% 2.33/0.95  --min_unsat_core                        false
% 2.33/0.95  --soft_assumptions                      false
% 2.33/0.95  --soft_lemma_size                       3
% 2.33/0.95  --prop_impl_unit_size                   0
% 2.33/0.95  --prop_impl_unit                        []
% 2.33/0.95  --share_sel_clauses                     true
% 2.33/0.95  --reset_solvers                         false
% 2.33/0.95  --bc_imp_inh                            [conj_cone]
% 2.33/0.95  --conj_cone_tolerance                   3.
% 2.33/0.95  --extra_neg_conj                        none
% 2.33/0.95  --large_theory_mode                     true
% 2.33/0.95  --prolific_symb_bound                   200
% 2.33/0.95  --lt_threshold                          2000
% 2.33/0.95  --clause_weak_htbl                      true
% 2.33/0.95  --gc_record_bc_elim                     false
% 2.33/0.95  
% 2.33/0.95  ------ Preprocessing Options
% 2.33/0.95  
% 2.33/0.95  --preprocessing_flag                    true
% 2.33/0.95  --time_out_prep_mult                    0.1
% 2.33/0.95  --splitting_mode                        input
% 2.33/0.95  --splitting_grd                         true
% 2.33/0.95  --splitting_cvd                         false
% 2.33/0.95  --splitting_cvd_svl                     false
% 2.33/0.95  --splitting_nvd                         32
% 2.33/0.95  --sub_typing                            true
% 2.33/0.95  --prep_gs_sim                           true
% 2.33/0.95  --prep_unflatten                        true
% 2.33/0.95  --prep_res_sim                          true
% 2.33/0.95  --prep_upred                            true
% 2.33/0.95  --prep_sem_filter                       exhaustive
% 2.33/0.95  --prep_sem_filter_out                   false
% 2.33/0.95  --pred_elim                             true
% 2.33/0.95  --res_sim_input                         true
% 2.33/0.95  --eq_ax_congr_red                       true
% 2.33/0.95  --pure_diseq_elim                       true
% 2.33/0.95  --brand_transform                       false
% 2.33/0.95  --non_eq_to_eq                          false
% 2.33/0.95  --prep_def_merge                        true
% 2.33/0.95  --prep_def_merge_prop_impl              false
% 2.33/0.95  --prep_def_merge_mbd                    true
% 2.33/0.95  --prep_def_merge_tr_red                 false
% 2.33/0.95  --prep_def_merge_tr_cl                  false
% 2.33/0.95  --smt_preprocessing                     true
% 2.33/0.95  --smt_ac_axioms                         fast
% 2.33/0.95  --preprocessed_out                      false
% 2.33/0.95  --preprocessed_stats                    false
% 2.33/0.95  
% 2.33/0.95  ------ Abstraction refinement Options
% 2.33/0.95  
% 2.33/0.95  --abstr_ref                             []
% 2.33/0.95  --abstr_ref_prep                        false
% 2.33/0.95  --abstr_ref_until_sat                   false
% 2.33/0.95  --abstr_ref_sig_restrict                funpre
% 2.33/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.95  --abstr_ref_under                       []
% 2.33/0.95  
% 2.33/0.95  ------ SAT Options
% 2.33/0.95  
% 2.33/0.95  --sat_mode                              false
% 2.33/0.95  --sat_fm_restart_options                ""
% 2.33/0.95  --sat_gr_def                            false
% 2.33/0.95  --sat_epr_types                         true
% 2.33/0.95  --sat_non_cyclic_types                  false
% 2.33/0.95  --sat_finite_models                     false
% 2.33/0.95  --sat_fm_lemmas                         false
% 2.33/0.95  --sat_fm_prep                           false
% 2.33/0.95  --sat_fm_uc_incr                        true
% 2.33/0.95  --sat_out_model                         small
% 2.33/0.95  --sat_out_clauses                       false
% 2.33/0.95  
% 2.33/0.95  ------ QBF Options
% 2.33/0.95  
% 2.33/0.95  --qbf_mode                              false
% 2.33/0.95  --qbf_elim_univ                         false
% 2.33/0.95  --qbf_dom_inst                          none
% 2.33/0.95  --qbf_dom_pre_inst                      false
% 2.33/0.95  --qbf_sk_in                             false
% 2.33/0.95  --qbf_pred_elim                         true
% 2.33/0.95  --qbf_split                             512
% 2.33/0.95  
% 2.33/0.95  ------ BMC1 Options
% 2.33/0.95  
% 2.33/0.95  --bmc1_incremental                      false
% 2.33/0.95  --bmc1_axioms                           reachable_all
% 2.33/0.95  --bmc1_min_bound                        0
% 2.33/0.95  --bmc1_max_bound                        -1
% 2.33/0.95  --bmc1_max_bound_default                -1
% 2.33/0.95  --bmc1_symbol_reachability              true
% 2.33/0.95  --bmc1_property_lemmas                  false
% 2.33/0.95  --bmc1_k_induction                      false
% 2.33/0.95  --bmc1_non_equiv_states                 false
% 2.33/0.95  --bmc1_deadlock                         false
% 2.33/0.95  --bmc1_ucm                              false
% 2.33/0.95  --bmc1_add_unsat_core                   none
% 2.33/0.95  --bmc1_unsat_core_children              false
% 2.33/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.95  --bmc1_out_stat                         full
% 2.33/0.95  --bmc1_ground_init                      false
% 2.33/0.95  --bmc1_pre_inst_next_state              false
% 2.33/0.95  --bmc1_pre_inst_state                   false
% 2.33/0.95  --bmc1_pre_inst_reach_state             false
% 2.33/0.95  --bmc1_out_unsat_core                   false
% 2.33/0.95  --bmc1_aig_witness_out                  false
% 2.33/0.95  --bmc1_verbose                          false
% 2.33/0.95  --bmc1_dump_clauses_tptp                false
% 2.33/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.95  --bmc1_dump_file                        -
% 2.33/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.95  --bmc1_ucm_extend_mode                  1
% 2.33/0.95  --bmc1_ucm_init_mode                    2
% 2.33/0.95  --bmc1_ucm_cone_mode                    none
% 2.33/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.95  --bmc1_ucm_relax_model                  4
% 2.33/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.95  --bmc1_ucm_layered_model                none
% 2.33/0.95  --bmc1_ucm_max_lemma_size               10
% 2.33/0.95  
% 2.33/0.95  ------ AIG Options
% 2.33/0.95  
% 2.33/0.95  --aig_mode                              false
% 2.33/0.95  
% 2.33/0.95  ------ Instantiation Options
% 2.33/0.95  
% 2.33/0.95  --instantiation_flag                    true
% 2.33/0.95  --inst_sos_flag                         false
% 2.33/0.95  --inst_sos_phase                        true
% 2.33/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.95  --inst_lit_sel_side                     num_symb
% 2.33/0.95  --inst_solver_per_active                1400
% 2.33/0.95  --inst_solver_calls_frac                1.
% 2.33/0.95  --inst_passive_queue_type               priority_queues
% 2.33/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.95  --inst_passive_queues_freq              [25;2]
% 2.33/0.95  --inst_dismatching                      true
% 2.33/0.95  --inst_eager_unprocessed_to_passive     true
% 2.33/0.95  --inst_prop_sim_given                   true
% 2.33/0.95  --inst_prop_sim_new                     false
% 2.33/0.95  --inst_subs_new                         false
% 2.33/0.95  --inst_eq_res_simp                      false
% 2.33/0.95  --inst_subs_given                       false
% 2.33/0.95  --inst_orphan_elimination               true
% 2.33/0.95  --inst_learning_loop_flag               true
% 2.33/0.95  --inst_learning_start                   3000
% 2.33/0.95  --inst_learning_factor                  2
% 2.33/0.95  --inst_start_prop_sim_after_learn       3
% 2.33/0.95  --inst_sel_renew                        solver
% 2.33/0.95  --inst_lit_activity_flag                true
% 2.33/0.95  --inst_restr_to_given                   false
% 2.33/0.95  --inst_activity_threshold               500
% 2.33/0.95  --inst_out_proof                        true
% 2.33/0.95  
% 2.33/0.95  ------ Resolution Options
% 2.33/0.95  
% 2.33/0.95  --resolution_flag                       true
% 2.33/0.95  --res_lit_sel                           adaptive
% 2.33/0.95  --res_lit_sel_side                      none
% 2.33/0.95  --res_ordering                          kbo
% 2.33/0.95  --res_to_prop_solver                    active
% 2.33/0.95  --res_prop_simpl_new                    false
% 2.33/0.95  --res_prop_simpl_given                  true
% 2.33/0.95  --res_passive_queue_type                priority_queues
% 2.33/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.95  --res_passive_queues_freq               [15;5]
% 2.33/0.95  --res_forward_subs                      full
% 2.33/0.95  --res_backward_subs                     full
% 2.33/0.95  --res_forward_subs_resolution           true
% 2.33/0.95  --res_backward_subs_resolution          true
% 2.33/0.95  --res_orphan_elimination                true
% 2.33/0.95  --res_time_limit                        2.
% 2.33/0.95  --res_out_proof                         true
% 2.33/0.95  
% 2.33/0.95  ------ Superposition Options
% 2.33/0.95  
% 2.33/0.95  --superposition_flag                    true
% 2.33/0.95  --sup_passive_queue_type                priority_queues
% 2.33/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.95  --demod_completeness_check              fast
% 2.33/0.95  --demod_use_ground                      true
% 2.33/0.95  --sup_to_prop_solver                    passive
% 2.33/0.95  --sup_prop_simpl_new                    true
% 2.33/0.95  --sup_prop_simpl_given                  true
% 2.33/0.95  --sup_fun_splitting                     false
% 2.33/0.95  --sup_smt_interval                      50000
% 2.33/0.95  
% 2.33/0.95  ------ Superposition Simplification Setup
% 2.33/0.95  
% 2.33/0.95  --sup_indices_passive                   []
% 2.33/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.95  --sup_full_bw                           [BwDemod]
% 2.33/0.95  --sup_immed_triv                        [TrivRules]
% 2.33/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.95  --sup_immed_bw_main                     []
% 2.33/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.95  
% 2.33/0.95  ------ Combination Options
% 2.33/0.95  
% 2.33/0.95  --comb_res_mult                         3
% 2.33/0.95  --comb_sup_mult                         2
% 2.33/0.95  --comb_inst_mult                        10
% 2.33/0.95  
% 2.33/0.95  ------ Debug Options
% 2.33/0.95  
% 2.33/0.95  --dbg_backtrace                         false
% 2.33/0.95  --dbg_dump_prop_clauses                 false
% 2.33/0.95  --dbg_dump_prop_clauses_file            -
% 2.33/0.95  --dbg_out_stat                          false
% 2.33/0.95  ------ Parsing...
% 2.33/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.95  
% 2.33/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.33/0.95  
% 2.33/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.95  
% 2.33/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.95  ------ Proving...
% 2.33/0.95  ------ Problem Properties 
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  clauses                                 21
% 2.33/0.95  conjectures                             2
% 2.33/0.95  EPR                                     1
% 2.33/0.95  Horn                                    17
% 2.33/0.95  unary                                   7
% 2.33/0.95  binary                                  7
% 2.33/0.95  lits                                    45
% 2.33/0.95  lits eq                                 25
% 2.33/0.95  fd_pure                                 0
% 2.33/0.95  fd_pseudo                               0
% 2.33/0.95  fd_cond                                 0
% 2.33/0.95  fd_pseudo_cond                          6
% 2.33/0.95  AC symbols                              0
% 2.33/0.95  
% 2.33/0.95  ------ Schedule dynamic 5 is on 
% 2.33/0.95  
% 2.33/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  ------ 
% 2.33/0.95  Current options:
% 2.33/0.95  ------ 
% 2.33/0.95  
% 2.33/0.95  ------ Input Options
% 2.33/0.95  
% 2.33/0.95  --out_options                           all
% 2.33/0.95  --tptp_safe_out                         true
% 2.33/0.95  --problem_path                          ""
% 2.33/0.95  --include_path                          ""
% 2.33/0.95  --clausifier                            res/vclausify_rel
% 2.33/0.95  --clausifier_options                    --mode clausify
% 2.33/0.95  --stdin                                 false
% 2.33/0.95  --stats_out                             all
% 2.33/0.95  
% 2.33/0.95  ------ General Options
% 2.33/0.95  
% 2.33/0.95  --fof                                   false
% 2.33/0.95  --time_out_real                         305.
% 2.33/0.95  --time_out_virtual                      -1.
% 2.33/0.95  --symbol_type_check                     false
% 2.33/0.95  --clausify_out                          false
% 2.33/0.95  --sig_cnt_out                           false
% 2.33/0.95  --trig_cnt_out                          false
% 2.33/0.95  --trig_cnt_out_tolerance                1.
% 2.33/0.95  --trig_cnt_out_sk_spl                   false
% 2.33/0.95  --abstr_cl_out                          false
% 2.33/0.95  
% 2.33/0.95  ------ Global Options
% 2.33/0.95  
% 2.33/0.95  --schedule                              default
% 2.33/0.95  --add_important_lit                     false
% 2.33/0.95  --prop_solver_per_cl                    1000
% 2.33/0.95  --min_unsat_core                        false
% 2.33/0.95  --soft_assumptions                      false
% 2.33/0.95  --soft_lemma_size                       3
% 2.33/0.95  --prop_impl_unit_size                   0
% 2.33/0.95  --prop_impl_unit                        []
% 2.33/0.95  --share_sel_clauses                     true
% 2.33/0.95  --reset_solvers                         false
% 2.33/0.95  --bc_imp_inh                            [conj_cone]
% 2.33/0.95  --conj_cone_tolerance                   3.
% 2.33/0.95  --extra_neg_conj                        none
% 2.33/0.95  --large_theory_mode                     true
% 2.33/0.95  --prolific_symb_bound                   200
% 2.33/0.95  --lt_threshold                          2000
% 2.33/0.95  --clause_weak_htbl                      true
% 2.33/0.95  --gc_record_bc_elim                     false
% 2.33/0.95  
% 2.33/0.95  ------ Preprocessing Options
% 2.33/0.95  
% 2.33/0.95  --preprocessing_flag                    true
% 2.33/0.95  --time_out_prep_mult                    0.1
% 2.33/0.95  --splitting_mode                        input
% 2.33/0.95  --splitting_grd                         true
% 2.33/0.95  --splitting_cvd                         false
% 2.33/0.95  --splitting_cvd_svl                     false
% 2.33/0.95  --splitting_nvd                         32
% 2.33/0.95  --sub_typing                            true
% 2.33/0.95  --prep_gs_sim                           true
% 2.33/0.95  --prep_unflatten                        true
% 2.33/0.95  --prep_res_sim                          true
% 2.33/0.95  --prep_upred                            true
% 2.33/0.95  --prep_sem_filter                       exhaustive
% 2.33/0.95  --prep_sem_filter_out                   false
% 2.33/0.95  --pred_elim                             true
% 2.33/0.95  --res_sim_input                         true
% 2.33/0.95  --eq_ax_congr_red                       true
% 2.33/0.95  --pure_diseq_elim                       true
% 2.33/0.95  --brand_transform                       false
% 2.33/0.95  --non_eq_to_eq                          false
% 2.33/0.95  --prep_def_merge                        true
% 2.33/0.95  --prep_def_merge_prop_impl              false
% 2.33/0.95  --prep_def_merge_mbd                    true
% 2.33/0.95  --prep_def_merge_tr_red                 false
% 2.33/0.95  --prep_def_merge_tr_cl                  false
% 2.33/0.95  --smt_preprocessing                     true
% 2.33/0.95  --smt_ac_axioms                         fast
% 2.33/0.95  --preprocessed_out                      false
% 2.33/0.95  --preprocessed_stats                    false
% 2.33/0.95  
% 2.33/0.95  ------ Abstraction refinement Options
% 2.33/0.95  
% 2.33/0.95  --abstr_ref                             []
% 2.33/0.95  --abstr_ref_prep                        false
% 2.33/0.95  --abstr_ref_until_sat                   false
% 2.33/0.95  --abstr_ref_sig_restrict                funpre
% 2.33/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.95  --abstr_ref_under                       []
% 2.33/0.95  
% 2.33/0.95  ------ SAT Options
% 2.33/0.95  
% 2.33/0.95  --sat_mode                              false
% 2.33/0.95  --sat_fm_restart_options                ""
% 2.33/0.95  --sat_gr_def                            false
% 2.33/0.95  --sat_epr_types                         true
% 2.33/0.95  --sat_non_cyclic_types                  false
% 2.33/0.95  --sat_finite_models                     false
% 2.33/0.95  --sat_fm_lemmas                         false
% 2.33/0.95  --sat_fm_prep                           false
% 2.33/0.95  --sat_fm_uc_incr                        true
% 2.33/0.95  --sat_out_model                         small
% 2.33/0.95  --sat_out_clauses                       false
% 2.33/0.95  
% 2.33/0.95  ------ QBF Options
% 2.33/0.95  
% 2.33/0.95  --qbf_mode                              false
% 2.33/0.95  --qbf_elim_univ                         false
% 2.33/0.95  --qbf_dom_inst                          none
% 2.33/0.95  --qbf_dom_pre_inst                      false
% 2.33/0.95  --qbf_sk_in                             false
% 2.33/0.95  --qbf_pred_elim                         true
% 2.33/0.95  --qbf_split                             512
% 2.33/0.95  
% 2.33/0.95  ------ BMC1 Options
% 2.33/0.95  
% 2.33/0.95  --bmc1_incremental                      false
% 2.33/0.95  --bmc1_axioms                           reachable_all
% 2.33/0.95  --bmc1_min_bound                        0
% 2.33/0.95  --bmc1_max_bound                        -1
% 2.33/0.95  --bmc1_max_bound_default                -1
% 2.33/0.95  --bmc1_symbol_reachability              true
% 2.33/0.95  --bmc1_property_lemmas                  false
% 2.33/0.95  --bmc1_k_induction                      false
% 2.33/0.95  --bmc1_non_equiv_states                 false
% 2.33/0.95  --bmc1_deadlock                         false
% 2.33/0.95  --bmc1_ucm                              false
% 2.33/0.95  --bmc1_add_unsat_core                   none
% 2.33/0.95  --bmc1_unsat_core_children              false
% 2.33/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.95  --bmc1_out_stat                         full
% 2.33/0.95  --bmc1_ground_init                      false
% 2.33/0.95  --bmc1_pre_inst_next_state              false
% 2.33/0.95  --bmc1_pre_inst_state                   false
% 2.33/0.95  --bmc1_pre_inst_reach_state             false
% 2.33/0.95  --bmc1_out_unsat_core                   false
% 2.33/0.95  --bmc1_aig_witness_out                  false
% 2.33/0.95  --bmc1_verbose                          false
% 2.33/0.95  --bmc1_dump_clauses_tptp                false
% 2.33/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.95  --bmc1_dump_file                        -
% 2.33/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.95  --bmc1_ucm_extend_mode                  1
% 2.33/0.95  --bmc1_ucm_init_mode                    2
% 2.33/0.95  --bmc1_ucm_cone_mode                    none
% 2.33/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.95  --bmc1_ucm_relax_model                  4
% 2.33/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.95  --bmc1_ucm_layered_model                none
% 2.33/0.95  --bmc1_ucm_max_lemma_size               10
% 2.33/0.95  
% 2.33/0.95  ------ AIG Options
% 2.33/0.95  
% 2.33/0.95  --aig_mode                              false
% 2.33/0.95  
% 2.33/0.95  ------ Instantiation Options
% 2.33/0.95  
% 2.33/0.95  --instantiation_flag                    true
% 2.33/0.95  --inst_sos_flag                         false
% 2.33/0.95  --inst_sos_phase                        true
% 2.33/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.95  --inst_lit_sel_side                     none
% 2.33/0.95  --inst_solver_per_active                1400
% 2.33/0.95  --inst_solver_calls_frac                1.
% 2.33/0.95  --inst_passive_queue_type               priority_queues
% 2.33/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.95  --inst_passive_queues_freq              [25;2]
% 2.33/0.95  --inst_dismatching                      true
% 2.33/0.95  --inst_eager_unprocessed_to_passive     true
% 2.33/0.95  --inst_prop_sim_given                   true
% 2.33/0.95  --inst_prop_sim_new                     false
% 2.33/0.95  --inst_subs_new                         false
% 2.33/0.95  --inst_eq_res_simp                      false
% 2.33/0.95  --inst_subs_given                       false
% 2.33/0.95  --inst_orphan_elimination               true
% 2.33/0.95  --inst_learning_loop_flag               true
% 2.33/0.95  --inst_learning_start                   3000
% 2.33/0.95  --inst_learning_factor                  2
% 2.33/0.95  --inst_start_prop_sim_after_learn       3
% 2.33/0.95  --inst_sel_renew                        solver
% 2.33/0.95  --inst_lit_activity_flag                true
% 2.33/0.95  --inst_restr_to_given                   false
% 2.33/0.95  --inst_activity_threshold               500
% 2.33/0.95  --inst_out_proof                        true
% 2.33/0.95  
% 2.33/0.95  ------ Resolution Options
% 2.33/0.95  
% 2.33/0.95  --resolution_flag                       false
% 2.33/0.95  --res_lit_sel                           adaptive
% 2.33/0.95  --res_lit_sel_side                      none
% 2.33/0.95  --res_ordering                          kbo
% 2.33/0.95  --res_to_prop_solver                    active
% 2.33/0.95  --res_prop_simpl_new                    false
% 2.33/0.95  --res_prop_simpl_given                  true
% 2.33/0.95  --res_passive_queue_type                priority_queues
% 2.33/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.95  --res_passive_queues_freq               [15;5]
% 2.33/0.95  --res_forward_subs                      full
% 2.33/0.95  --res_backward_subs                     full
% 2.33/0.95  --res_forward_subs_resolution           true
% 2.33/0.95  --res_backward_subs_resolution          true
% 2.33/0.95  --res_orphan_elimination                true
% 2.33/0.95  --res_time_limit                        2.
% 2.33/0.95  --res_out_proof                         true
% 2.33/0.95  
% 2.33/0.95  ------ Superposition Options
% 2.33/0.95  
% 2.33/0.95  --superposition_flag                    true
% 2.33/0.95  --sup_passive_queue_type                priority_queues
% 2.33/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.95  --demod_completeness_check              fast
% 2.33/0.95  --demod_use_ground                      true
% 2.33/0.95  --sup_to_prop_solver                    passive
% 2.33/0.95  --sup_prop_simpl_new                    true
% 2.33/0.95  --sup_prop_simpl_given                  true
% 2.33/0.95  --sup_fun_splitting                     false
% 2.33/0.95  --sup_smt_interval                      50000
% 2.33/0.95  
% 2.33/0.95  ------ Superposition Simplification Setup
% 2.33/0.95  
% 2.33/0.95  --sup_indices_passive                   []
% 2.33/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.95  --sup_full_bw                           [BwDemod]
% 2.33/0.95  --sup_immed_triv                        [TrivRules]
% 2.33/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.95  --sup_immed_bw_main                     []
% 2.33/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.95  
% 2.33/0.95  ------ Combination Options
% 2.33/0.95  
% 2.33/0.95  --comb_res_mult                         3
% 2.33/0.95  --comb_sup_mult                         2
% 2.33/0.95  --comb_inst_mult                        10
% 2.33/0.95  
% 2.33/0.95  ------ Debug Options
% 2.33/0.95  
% 2.33/0.95  --dbg_backtrace                         false
% 2.33/0.95  --dbg_dump_prop_clauses                 false
% 2.33/0.95  --dbg_dump_prop_clauses_file            -
% 2.33/0.95  --dbg_out_stat                          false
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  ------ Proving...
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  % SZS status Theorem for theBenchmark.p
% 2.33/0.95  
% 2.33/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.95  
% 2.33/0.95  fof(f12,axiom,(
% 2.33/0.95    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f17,plain,(
% 2.33/0.95    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.33/0.95    inference(ennf_transformation,[],[f12])).
% 2.33/0.95  
% 2.33/0.95  fof(f54,plain,(
% 2.33/0.95    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f17])).
% 2.33/0.95  
% 2.33/0.95  fof(f8,axiom,(
% 2.33/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f50,plain,(
% 2.33/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f8])).
% 2.33/0.95  
% 2.33/0.95  fof(f9,axiom,(
% 2.33/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f51,plain,(
% 2.33/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f9])).
% 2.33/0.95  
% 2.33/0.95  fof(f10,axiom,(
% 2.33/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f52,plain,(
% 2.33/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f10])).
% 2.33/0.95  
% 2.33/0.95  fof(f57,plain,(
% 2.33/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.33/0.95    inference(definition_unfolding,[],[f51,f52])).
% 2.33/0.95  
% 2.33/0.95  fof(f58,plain,(
% 2.33/0.95    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.33/0.95    inference(definition_unfolding,[],[f50,f57])).
% 2.33/0.95  
% 2.33/0.95  fof(f74,plain,(
% 2.33/0.95    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.33/0.95    inference(definition_unfolding,[],[f54,f58])).
% 2.33/0.95  
% 2.33/0.95  fof(f1,axiom,(
% 2.33/0.95    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f19,plain,(
% 2.33/0.95    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.33/0.95    inference(nnf_transformation,[],[f1])).
% 2.33/0.95  
% 2.33/0.95  fof(f32,plain,(
% 2.33/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f19])).
% 2.33/0.95  
% 2.33/0.95  fof(f7,axiom,(
% 2.33/0.95    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f25,plain,(
% 2.33/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.33/0.95    inference(nnf_transformation,[],[f7])).
% 2.33/0.95  
% 2.33/0.95  fof(f26,plain,(
% 2.33/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.33/0.95    inference(rectify,[],[f25])).
% 2.33/0.95  
% 2.33/0.95  fof(f27,plain,(
% 2.33/0.95    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.33/0.95    introduced(choice_axiom,[])).
% 2.33/0.95  
% 2.33/0.95  fof(f28,plain,(
% 2.33/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.33/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.33/0.95  
% 2.33/0.95  fof(f46,plain,(
% 2.33/0.95    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.33/0.95    inference(cnf_transformation,[],[f28])).
% 2.33/0.95  
% 2.33/0.95  fof(f72,plain,(
% 2.33/0.95    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.33/0.95    inference(definition_unfolding,[],[f46,f58])).
% 2.33/0.95  
% 2.33/0.95  fof(f86,plain,(
% 2.33/0.95    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 2.33/0.95    inference(equality_resolution,[],[f72])).
% 2.33/0.95  
% 2.33/0.95  fof(f13,conjecture,(
% 2.33/0.95    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f14,negated_conjecture,(
% 2.33/0.95    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.33/0.95    inference(negated_conjecture,[],[f13])).
% 2.33/0.95  
% 2.33/0.95  fof(f18,plain,(
% 2.33/0.95    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 2.33/0.95    inference(ennf_transformation,[],[f14])).
% 2.33/0.95  
% 2.33/0.95  fof(f29,plain,(
% 2.33/0.95    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 2.33/0.95    inference(nnf_transformation,[],[f18])).
% 2.33/0.95  
% 2.33/0.95  fof(f30,plain,(
% 2.33/0.95    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)) & (sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)))),
% 2.33/0.95    introduced(choice_axiom,[])).
% 2.33/0.95  
% 2.33/0.95  fof(f31,plain,(
% 2.33/0.95    (sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)) & (sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 2.33/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).
% 2.33/0.95  
% 2.33/0.95  fof(f56,plain,(
% 2.33/0.95    sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)),
% 2.33/0.95    inference(cnf_transformation,[],[f31])).
% 2.33/0.95  
% 2.33/0.95  fof(f2,axiom,(
% 2.33/0.95    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f34,plain,(
% 2.33/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.33/0.95    inference(cnf_transformation,[],[f2])).
% 2.33/0.95  
% 2.33/0.95  fof(f75,plain,(
% 2.33/0.95    sK2 = sK3 | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 2.33/0.95    inference(definition_unfolding,[],[f56,f34,f58,f58,f58])).
% 2.33/0.95  
% 2.33/0.95  fof(f4,axiom,(
% 2.33/0.95    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f36,plain,(
% 2.33/0.95    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f4])).
% 2.33/0.95  
% 2.33/0.95  fof(f3,axiom,(
% 2.33/0.95    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f35,plain,(
% 2.33/0.95    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.33/0.95    inference(cnf_transformation,[],[f3])).
% 2.33/0.95  
% 2.33/0.95  fof(f59,plain,(
% 2.33/0.95    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.33/0.95    inference(definition_unfolding,[],[f35,f34])).
% 2.33/0.95  
% 2.33/0.95  fof(f55,plain,(
% 2.33/0.95    sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 2.33/0.95    inference(cnf_transformation,[],[f31])).
% 2.33/0.95  
% 2.33/0.95  fof(f76,plain,(
% 2.33/0.95    sK2 != sK3 | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 2.33/0.95    inference(definition_unfolding,[],[f55,f34,f58,f58,f58])).
% 2.33/0.95  
% 2.33/0.95  fof(f5,axiom,(
% 2.33/0.95    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f37,plain,(
% 2.33/0.95    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f5])).
% 2.33/0.95  
% 2.33/0.95  fof(f60,plain,(
% 2.33/0.95    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.33/0.95    inference(definition_unfolding,[],[f37,f34])).
% 2.33/0.95  
% 2.33/0.95  fof(f6,axiom,(
% 2.33/0.95    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f15,plain,(
% 2.33/0.95    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.33/0.95    inference(ennf_transformation,[],[f6])).
% 2.33/0.95  
% 2.33/0.95  fof(f20,plain,(
% 2.33/0.95    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/0.95    inference(nnf_transformation,[],[f15])).
% 2.33/0.95  
% 2.33/0.95  fof(f21,plain,(
% 2.33/0.95    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/0.95    inference(flattening,[],[f20])).
% 2.33/0.95  
% 2.33/0.95  fof(f22,plain,(
% 2.33/0.95    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/0.95    inference(rectify,[],[f21])).
% 2.33/0.95  
% 2.33/0.95  fof(f23,plain,(
% 2.33/0.95    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.33/0.95    introduced(choice_axiom,[])).
% 2.33/0.95  
% 2.33/0.95  fof(f24,plain,(
% 2.33/0.95    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.33/0.95  
% 2.33/0.95  fof(f41,plain,(
% 2.33/0.95    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.33/0.95    inference(cnf_transformation,[],[f24])).
% 2.33/0.95  
% 2.33/0.95  fof(f65,plain,(
% 2.33/0.95    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.33/0.95    inference(definition_unfolding,[],[f41,f52])).
% 2.33/0.95  
% 2.33/0.95  fof(f77,plain,(
% 2.33/0.95    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 2.33/0.95    inference(equality_resolution,[],[f65])).
% 2.33/0.95  
% 2.33/0.95  fof(f78,plain,(
% 2.33/0.95    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 2.33/0.95    inference(equality_resolution,[],[f77])).
% 2.33/0.95  
% 2.33/0.95  fof(f11,axiom,(
% 2.33/0.95    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.33/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.95  
% 2.33/0.95  fof(f16,plain,(
% 2.33/0.95    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.33/0.95    inference(ennf_transformation,[],[f11])).
% 2.33/0.95  
% 2.33/0.95  fof(f53,plain,(
% 2.33/0.95    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.33/0.95    inference(cnf_transformation,[],[f16])).
% 2.33/0.95  
% 2.33/0.95  fof(f73,plain,(
% 2.33/0.95    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 2.33/0.95    inference(definition_unfolding,[],[f53,f58])).
% 2.33/0.95  
% 2.33/0.95  cnf(c_18,plain,
% 2.33/0.95      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.33/0.95      inference(cnf_transformation,[],[f74]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1425,plain,
% 2.33/0.95      ( r2_hidden(X0,X1) = iProver_top
% 2.33/0.95      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 2.33/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1,plain,
% 2.33/0.95      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.33/0.95      inference(cnf_transformation,[],[f32]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1441,plain,
% 2.33/0.95      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 2.33/0.95      | r1_xboole_0(X0,X1) != iProver_top ),
% 2.33/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1751,plain,
% 2.33/0.95      ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
% 2.33/0.95      | r2_hidden(X0,X1) = iProver_top ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_1425,c_1441]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_16,plain,
% 2.33/0.95      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 2.33/0.95      inference(cnf_transformation,[],[f86]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1427,plain,
% 2.33/0.95      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 2.33/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3003,plain,
% 2.33/0.95      ( X0 = X1
% 2.33/0.95      | k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_1751,c_1427]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_19,negated_conjecture,
% 2.33/0.95      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) != k2_enumset1(sK2,sK2,sK2,sK2)
% 2.33/0.95      | sK2 = sK3 ),
% 2.33/0.95      inference(cnf_transformation,[],[f75]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3025,plain,
% 2.33/0.95      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) != k2_enumset1(sK2,sK2,sK2,sK2)
% 2.33/0.95      | sK3 = sK2 ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_3003,c_19]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3,plain,
% 2.33/0.95      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.33/0.95      inference(cnf_transformation,[],[f36]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1440,plain,
% 2.33/0.95      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.33/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1749,plain,
% 2.33/0.95      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_1440,c_1441]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_2,plain,
% 2.33/0.95      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.33/0.95      inference(cnf_transformation,[],[f59]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_2014,plain,
% 2.33/0.95      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.33/0.95      inference(demodulation,[status(thm)],[c_1749,c_2]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3028,plain,
% 2.33/0.95      ( k2_enumset1(sK2,sK2,sK2,sK2) != k2_enumset1(sK2,sK2,sK2,sK2)
% 2.33/0.95      | sK3 = sK2 ),
% 2.33/0.95      inference(demodulation,[status(thm)],[c_3025,c_2014]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3029,plain,
% 2.33/0.95      ( sK3 = sK2 ),
% 2.33/0.95      inference(equality_resolution_simp,[status(thm)],[c_3028]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_20,negated_conjecture,
% 2.33/0.95      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2)
% 2.33/0.95      | sK2 != sK3 ),
% 2.33/0.95      inference(cnf_transformation,[],[f76]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3120,plain,
% 2.33/0.95      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK2,sK2,sK2,sK2)
% 2.33/0.95      | sK2 != sK2 ),
% 2.33/0.95      inference(demodulation,[status(thm)],[c_3029,c_20]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_3122,plain,
% 2.33/0.95      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 2.33/0.95      inference(equality_resolution_simp,[status(thm)],[c_3120]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_4,plain,
% 2.33/0.95      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 2.33/0.95      inference(cnf_transformation,[],[f60]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1439,plain,
% 2.33/0.95      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 2.33/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_1750,plain,
% 2.33/0.95      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_1439,c_1441]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_4067,plain,
% 2.33/0.95      ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_3122,c_1750]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_4086,plain,
% 2.33/0.95      ( r1_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.33/0.95      inference(superposition,[status(thm)],[c_4067,c_1439]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_4088,plain,
% 2.33/0.95      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.33/0.95      inference(demodulation,[status(thm)],[c_4086,c_2014]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_9,plain,
% 2.33/0.95      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 2.33/0.95      inference(cnf_transformation,[],[f78]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_17,plain,
% 2.33/0.95      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.33/0.95      inference(cnf_transformation,[],[f73]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_145,plain,
% 2.33/0.95      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.33/0.95      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_655,plain,
% 2.33/0.95      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
% 2.33/0.95      | X0 != X2
% 2.33/0.95      | k2_enumset1(X3,X3,X4,X2) != X1 ),
% 2.33/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_145]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_656,plain,
% 2.33/0.95      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) ),
% 2.33/0.95      inference(unflattening,[status(thm)],[c_655]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_657,plain,
% 2.33/0.95      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) != iProver_top ),
% 2.33/0.95      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(c_659,plain,
% 2.33/0.95      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.33/0.95      inference(instantiation,[status(thm)],[c_657]) ).
% 2.33/0.95  
% 2.33/0.95  cnf(contradiction,plain,
% 2.33/0.95      ( $false ),
% 2.33/0.95      inference(minisat,[status(thm)],[c_4088,c_659]) ).
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.95  
% 2.33/0.95  ------                               Statistics
% 2.33/0.95  
% 2.33/0.95  ------ General
% 2.33/0.95  
% 2.33/0.95  abstr_ref_over_cycles:                  0
% 2.33/0.95  abstr_ref_under_cycles:                 0
% 2.33/0.95  gc_basic_clause_elim:                   0
% 2.33/0.95  forced_gc_time:                         0
% 2.33/0.95  parsing_time:                           0.009
% 2.33/0.95  unif_index_cands_time:                  0.
% 2.33/0.95  unif_index_add_time:                    0.
% 2.33/0.95  orderings_time:                         0.
% 2.33/0.95  out_proof_time:                         0.007
% 2.33/0.95  total_time:                             0.147
% 2.33/0.95  num_of_symbols:                         41
% 2.33/0.95  num_of_terms:                           3985
% 2.33/0.95  
% 2.33/0.95  ------ Preprocessing
% 2.33/0.95  
% 2.33/0.95  num_of_splits:                          0
% 2.33/0.95  num_of_split_atoms:                     0
% 2.33/0.95  num_of_reused_defs:                     0
% 2.33/0.95  num_eq_ax_congr_red:                    12
% 2.33/0.95  num_of_sem_filtered_clauses:            1
% 2.33/0.95  num_of_subtypes:                        0
% 2.33/0.95  monotx_restored_types:                  0
% 2.33/0.95  sat_num_of_epr_types:                   0
% 2.33/0.95  sat_num_of_non_cyclic_types:            0
% 2.33/0.95  sat_guarded_non_collapsed_types:        0
% 2.33/0.95  num_pure_diseq_elim:                    0
% 2.33/0.95  simp_replaced_by:                       0
% 2.33/0.95  res_preprocessed:                       78
% 2.33/0.95  prep_upred:                             0
% 2.33/0.95  prep_unflattend:                        71
% 2.33/0.95  smt_new_axioms:                         0
% 2.33/0.95  pred_elim_cands:                        2
% 2.33/0.95  pred_elim:                              0
% 2.33/0.95  pred_elim_cl:                           0
% 2.33/0.95  pred_elim_cycles:                       2
% 2.33/0.95  merged_defs:                            18
% 2.33/0.95  merged_defs_ncl:                        0
% 2.33/0.95  bin_hyper_res:                          18
% 2.33/0.95  prep_cycles:                            3
% 2.33/0.95  pred_elim_time:                         0.011
% 2.33/0.95  splitting_time:                         0.
% 2.33/0.95  sem_filter_time:                        0.
% 2.33/0.95  monotx_time:                            0.001
% 2.33/0.95  subtype_inf_time:                       0.
% 2.33/0.95  
% 2.33/0.95  ------ Problem properties
% 2.33/0.95  
% 2.33/0.95  clauses:                                21
% 2.33/0.95  conjectures:                            2
% 2.33/0.95  epr:                                    1
% 2.33/0.95  horn:                                   17
% 2.33/0.95  ground:                                 2
% 2.33/0.95  unary:                                  7
% 2.33/0.95  binary:                                 7
% 2.33/0.95  lits:                                   45
% 2.33/0.95  lits_eq:                                25
% 2.33/0.95  fd_pure:                                0
% 2.33/0.95  fd_pseudo:                              0
% 2.33/0.95  fd_cond:                                0
% 2.33/0.95  fd_pseudo_cond:                         6
% 2.33/0.95  ac_symbols:                             0
% 2.33/0.95  
% 2.33/0.95  ------ Propositional Solver
% 2.33/0.95  
% 2.33/0.95  prop_solver_calls:                      23
% 2.33/0.95  prop_fast_solver_calls:                 595
% 2.33/0.95  smt_solver_calls:                       0
% 2.33/0.95  smt_fast_solver_calls:                  0
% 2.33/0.95  prop_num_of_clauses:                    1252
% 2.33/0.95  prop_preprocess_simplified:             4177
% 2.33/0.95  prop_fo_subsumed:                       4
% 2.33/0.95  prop_solver_time:                       0.
% 2.33/0.95  smt_solver_time:                        0.
% 2.33/0.95  smt_fast_solver_time:                   0.
% 2.33/0.95  prop_fast_solver_time:                  0.
% 2.33/0.95  prop_unsat_core_time:                   0.
% 2.33/0.95  
% 2.33/0.95  ------ QBF
% 2.33/0.95  
% 2.33/0.95  qbf_q_res:                              0
% 2.33/0.95  qbf_num_tautologies:                    0
% 2.33/0.95  qbf_prep_cycles:                        0
% 2.33/0.95  
% 2.33/0.95  ------ BMC1
% 2.33/0.95  
% 2.33/0.95  bmc1_current_bound:                     -1
% 2.33/0.95  bmc1_last_solved_bound:                 -1
% 2.33/0.95  bmc1_unsat_core_size:                   -1
% 2.33/0.95  bmc1_unsat_core_parents_size:           -1
% 2.33/0.95  bmc1_merge_next_fun:                    0
% 2.33/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.95  
% 2.33/0.95  ------ Instantiation
% 2.33/0.95  
% 2.33/0.95  inst_num_of_clauses:                    393
% 2.33/0.95  inst_num_in_passive:                    100
% 2.33/0.95  inst_num_in_active:                     146
% 2.33/0.95  inst_num_in_unprocessed:                147
% 2.33/0.95  inst_num_of_loops:                      190
% 2.33/0.95  inst_num_of_learning_restarts:          0
% 2.33/0.95  inst_num_moves_active_passive:          42
% 2.33/0.95  inst_lit_activity:                      0
% 2.33/0.95  inst_lit_activity_moves:                0
% 2.33/0.95  inst_num_tautologies:                   0
% 2.33/0.95  inst_num_prop_implied:                  0
% 2.33/0.95  inst_num_existing_simplified:           0
% 2.33/0.95  inst_num_eq_res_simplified:             0
% 2.33/0.95  inst_num_child_elim:                    0
% 2.33/0.95  inst_num_of_dismatching_blockings:      81
% 2.33/0.95  inst_num_of_non_proper_insts:           289
% 2.33/0.95  inst_num_of_duplicates:                 0
% 2.33/0.95  inst_inst_num_from_inst_to_res:         0
% 2.33/0.95  inst_dismatching_checking_time:         0.
% 2.33/0.95  
% 2.33/0.95  ------ Resolution
% 2.33/0.95  
% 2.33/0.95  res_num_of_clauses:                     0
% 2.33/0.95  res_num_in_passive:                     0
% 2.33/0.95  res_num_in_active:                      0
% 2.33/0.95  res_num_of_loops:                       81
% 2.33/0.95  res_forward_subset_subsumed:            78
% 2.33/0.95  res_backward_subset_subsumed:           0
% 2.33/0.95  res_forward_subsumed:                   6
% 2.33/0.95  res_backward_subsumed:                  0
% 2.33/0.95  res_forward_subsumption_resolution:     0
% 2.33/0.95  res_backward_subsumption_resolution:    0
% 2.33/0.95  res_clause_to_clause_subsumption:       588
% 2.33/0.95  res_orphan_elimination:                 0
% 2.33/0.95  res_tautology_del:                      64
% 2.33/0.95  res_num_eq_res_simplified:              0
% 2.33/0.95  res_num_sel_changes:                    0
% 2.33/0.95  res_moves_from_active_to_pass:          0
% 2.33/0.95  
% 2.33/0.95  ------ Superposition
% 2.33/0.95  
% 2.33/0.95  sup_time_total:                         0.
% 2.33/0.95  sup_time_generating:                    0.
% 2.33/0.95  sup_time_sim_full:                      0.
% 2.33/0.95  sup_time_sim_immed:                     0.
% 2.33/0.95  
% 2.33/0.95  sup_num_of_clauses:                     69
% 2.33/0.95  sup_num_in_active:                      33
% 2.33/0.95  sup_num_in_passive:                     36
% 2.33/0.95  sup_num_of_loops:                       37
% 2.33/0.95  sup_fw_superposition:                   75
% 2.33/0.95  sup_bw_superposition:                   79
% 2.33/0.95  sup_immediate_simplified:               31
% 2.33/0.95  sup_given_eliminated:                   1
% 2.33/0.95  comparisons_done:                       0
% 2.33/0.95  comparisons_avoided:                    15
% 2.33/0.95  
% 2.33/0.95  ------ Simplifications
% 2.33/0.95  
% 2.33/0.95  
% 2.33/0.95  sim_fw_subset_subsumed:                 13
% 2.33/0.95  sim_bw_subset_subsumed:                 2
% 2.33/0.95  sim_fw_subsumed:                        10
% 2.33/0.95  sim_bw_subsumed:                        1
% 2.33/0.95  sim_fw_subsumption_res:                 1
% 2.33/0.95  sim_bw_subsumption_res:                 0
% 2.33/0.95  sim_tautology_del:                      1
% 2.33/0.95  sim_eq_tautology_del:                   10
% 2.33/0.95  sim_eq_res_simp:                        3
% 2.33/0.95  sim_fw_demodulated:                     10
% 2.33/0.95  sim_bw_demodulated:                     5
% 2.33/0.95  sim_light_normalised:                   3
% 2.33/0.95  sim_joinable_taut:                      0
% 2.33/0.95  sim_joinable_simp:                      0
% 2.33/0.95  sim_ac_normalised:                      0
% 2.33/0.95  sim_smt_subsumption:                    0
% 2.33/0.95  
%------------------------------------------------------------------------------
