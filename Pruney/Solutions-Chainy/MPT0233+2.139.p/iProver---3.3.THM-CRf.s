%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:33 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  112 (1898 expanded)
%              Number of clauses        :   55 ( 256 expanded)
%              Number of leaves         :   12 ( 530 expanded)
%              Depth                    :   36
%              Number of atoms          :  361 (5957 expanded)
%              Number of equality atoms :  287 (4787 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f27,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f66,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f67,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f64,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f65,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f64])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f22])).

fof(f43,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f63,plain,(
    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f43,f47,f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X2) = X0
      | k3_enumset1(X2,X2,X2,X2,X2) = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f37,f47,f48,f48,f47])).

fof(f25,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f25,f46])).

fof(f70,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f44,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) ) ),
    inference(definition_unfolding,[],[f42,f47,f48])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | k3_enumset1(X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f39,f47,f48])).

fof(f73,plain,(
    ! [X2,X1] : r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f45,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f68,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f69,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f68])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_786,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_780,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_781,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_771,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | k3_enumset1(X1,X1,X1,X1,X2) = X0
    | k3_enumset1(X2,X2,X2,X2,X2) = X0
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_773,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = X2
    | k3_enumset1(X1,X1,X1,X1,X1) = X2
    | k3_enumset1(X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k3_enumset1(X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1977,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_771,c_773])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_778,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2034,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1977,c_778])).

cnf(c_2135,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK3 ),
    inference(superposition,[status(thm)],[c_781,c_2034])).

cnf(c_16,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_527,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_817,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_818,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_2136,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1 ),
    inference(superposition,[status(thm)],[c_780,c_2034])).

cnf(c_2264,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2135,c_16,c_20,c_29,c_818,c_2136])).

cnf(c_2265,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2264])).

cnf(c_2267,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | r2_hidden(sK4,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_781])).

cnf(c_2291,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK4
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_2267,c_778])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_807,plain,
    ( sK4 != X0
    | sK1 != X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_808,plain,
    ( sK4 != sK1
    | sK1 = sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_2470,plain,
    ( sK2 = sK4
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2291,c_15,c_20,c_29,c_808])).

cnf(c_2471,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK4 ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_7,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_779,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2472,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK4
    | r2_hidden(sK4,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_779])).

cnf(c_2506,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK4
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_2472,c_778])).

cnf(c_2884,plain,
    ( sK2 = sK4
    | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_15,c_20,c_29,c_808])).

cnf(c_2885,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK4 ),
    inference(renaming,[status(thm)],[c_2884])).

cnf(c_772,plain,
    ( X0 = X1
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2899,plain,
    ( sK2 = sK4
    | sK1 = X0
    | r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_772])).

cnf(c_4859,plain,
    ( sK2 = sK4
    | sK1 = X0 ),
    inference(superposition,[status(thm)],[c_786,c_2899])).

cnf(c_5019,plain,
    ( sK2 = sK4 ),
    inference(superposition,[status(thm)],[c_4859,c_15])).

cnf(c_5089,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK4)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5019,c_2265])).

cnf(c_5311,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
    | sK3 = X0
    | r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK4),k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_772])).

cnf(c_5310,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
    | sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_778])).

cnf(c_6199,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
    | sK3 = sK1
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_780,c_5310])).

cnf(c_6208,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5311,c_16,c_15,c_20,c_29,c_808,c_818,c_6199])).

cnf(c_6226,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6208,c_778])).

cnf(c_6774,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_780,c_6226])).

cnf(c_6781,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6774,c_15,c_20,c_29,c_808])).

cnf(c_6805,plain,
    ( sK1 = X0
    | r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6781,c_772])).

cnf(c_7319,plain,
    ( sK1 = X0 ),
    inference(superposition,[status(thm)],[c_786,c_6805])).

cnf(c_7359,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_7319,c_15])).

cnf(c_7362,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7359])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.68/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.93  
% 3.68/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.93  
% 3.68/0.93  ------  iProver source info
% 3.68/0.93  
% 3.68/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.93  git: non_committed_changes: false
% 3.68/0.93  git: last_make_outside_of_git: false
% 3.68/0.93  
% 3.68/0.93  ------ 
% 3.68/0.93  
% 3.68/0.93  ------ Input Options
% 3.68/0.93  
% 3.68/0.93  --out_options                           all
% 3.68/0.93  --tptp_safe_out                         true
% 3.68/0.93  --problem_path                          ""
% 3.68/0.93  --include_path                          ""
% 3.68/0.93  --clausifier                            res/vclausify_rel
% 3.68/0.93  --clausifier_options                    ""
% 3.68/0.93  --stdin                                 false
% 3.68/0.93  --stats_out                             all
% 3.68/0.93  
% 3.68/0.93  ------ General Options
% 3.68/0.93  
% 3.68/0.93  --fof                                   false
% 3.68/0.93  --time_out_real                         305.
% 3.68/0.93  --time_out_virtual                      -1.
% 3.68/0.93  --symbol_type_check                     false
% 3.68/0.93  --clausify_out                          false
% 3.68/0.93  --sig_cnt_out                           false
% 3.68/0.93  --trig_cnt_out                          false
% 3.68/0.93  --trig_cnt_out_tolerance                1.
% 3.68/0.93  --trig_cnt_out_sk_spl                   false
% 3.68/0.93  --abstr_cl_out                          false
% 3.68/0.93  
% 3.68/0.93  ------ Global Options
% 3.68/0.93  
% 3.68/0.93  --schedule                              default
% 3.68/0.93  --add_important_lit                     false
% 3.68/0.93  --prop_solver_per_cl                    1000
% 3.68/0.93  --min_unsat_core                        false
% 3.68/0.93  --soft_assumptions                      false
% 3.68/0.93  --soft_lemma_size                       3
% 3.68/0.93  --prop_impl_unit_size                   0
% 3.68/0.93  --prop_impl_unit                        []
% 3.68/0.93  --share_sel_clauses                     true
% 3.68/0.93  --reset_solvers                         false
% 3.68/0.93  --bc_imp_inh                            [conj_cone]
% 3.68/0.93  --conj_cone_tolerance                   3.
% 3.68/0.93  --extra_neg_conj                        none
% 3.68/0.93  --large_theory_mode                     true
% 3.68/0.93  --prolific_symb_bound                   200
% 3.68/0.93  --lt_threshold                          2000
% 3.68/0.93  --clause_weak_htbl                      true
% 3.68/0.93  --gc_record_bc_elim                     false
% 3.68/0.93  
% 3.68/0.93  ------ Preprocessing Options
% 3.68/0.93  
% 3.68/0.93  --preprocessing_flag                    true
% 3.68/0.93  --time_out_prep_mult                    0.1
% 3.68/0.93  --splitting_mode                        input
% 3.68/0.93  --splitting_grd                         true
% 3.68/0.93  --splitting_cvd                         false
% 3.68/0.93  --splitting_cvd_svl                     false
% 3.68/0.93  --splitting_nvd                         32
% 3.68/0.93  --sub_typing                            true
% 3.68/0.93  --prep_gs_sim                           true
% 3.68/0.93  --prep_unflatten                        true
% 3.68/0.93  --prep_res_sim                          true
% 3.68/0.93  --prep_upred                            true
% 3.68/0.93  --prep_sem_filter                       exhaustive
% 3.68/0.93  --prep_sem_filter_out                   false
% 3.68/0.93  --pred_elim                             true
% 3.68/0.93  --res_sim_input                         true
% 3.68/0.93  --eq_ax_congr_red                       true
% 3.68/0.93  --pure_diseq_elim                       true
% 3.68/0.93  --brand_transform                       false
% 3.68/0.93  --non_eq_to_eq                          false
% 3.68/0.93  --prep_def_merge                        true
% 3.68/0.93  --prep_def_merge_prop_impl              false
% 3.68/0.93  --prep_def_merge_mbd                    true
% 3.68/0.93  --prep_def_merge_tr_red                 false
% 3.68/0.93  --prep_def_merge_tr_cl                  false
% 3.68/0.93  --smt_preprocessing                     true
% 3.68/0.93  --smt_ac_axioms                         fast
% 3.68/0.93  --preprocessed_out                      false
% 3.68/0.93  --preprocessed_stats                    false
% 3.68/0.93  
% 3.68/0.93  ------ Abstraction refinement Options
% 3.68/0.93  
% 3.68/0.93  --abstr_ref                             []
% 3.68/0.93  --abstr_ref_prep                        false
% 3.68/0.93  --abstr_ref_until_sat                   false
% 3.68/0.93  --abstr_ref_sig_restrict                funpre
% 3.68/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.93  --abstr_ref_under                       []
% 3.68/0.93  
% 3.68/0.93  ------ SAT Options
% 3.68/0.93  
% 3.68/0.93  --sat_mode                              false
% 3.68/0.93  --sat_fm_restart_options                ""
% 3.68/0.93  --sat_gr_def                            false
% 3.68/0.93  --sat_epr_types                         true
% 3.68/0.93  --sat_non_cyclic_types                  false
% 3.68/0.93  --sat_finite_models                     false
% 3.68/0.93  --sat_fm_lemmas                         false
% 3.68/0.93  --sat_fm_prep                           false
% 3.68/0.93  --sat_fm_uc_incr                        true
% 3.68/0.93  --sat_out_model                         small
% 3.68/0.93  --sat_out_clauses                       false
% 3.68/0.93  
% 3.68/0.93  ------ QBF Options
% 3.68/0.93  
% 3.68/0.93  --qbf_mode                              false
% 3.68/0.93  --qbf_elim_univ                         false
% 3.68/0.93  --qbf_dom_inst                          none
% 3.68/0.93  --qbf_dom_pre_inst                      false
% 3.68/0.93  --qbf_sk_in                             false
% 3.68/0.93  --qbf_pred_elim                         true
% 3.68/0.93  --qbf_split                             512
% 3.68/0.93  
% 3.68/0.93  ------ BMC1 Options
% 3.68/0.93  
% 3.68/0.93  --bmc1_incremental                      false
% 3.68/0.93  --bmc1_axioms                           reachable_all
% 3.68/0.93  --bmc1_min_bound                        0
% 3.68/0.93  --bmc1_max_bound                        -1
% 3.68/0.93  --bmc1_max_bound_default                -1
% 3.68/0.93  --bmc1_symbol_reachability              true
% 3.68/0.93  --bmc1_property_lemmas                  false
% 3.68/0.93  --bmc1_k_induction                      false
% 3.68/0.93  --bmc1_non_equiv_states                 false
% 3.68/0.93  --bmc1_deadlock                         false
% 3.68/0.93  --bmc1_ucm                              false
% 3.68/0.93  --bmc1_add_unsat_core                   none
% 3.68/0.93  --bmc1_unsat_core_children              false
% 3.68/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.93  --bmc1_out_stat                         full
% 3.68/0.93  --bmc1_ground_init                      false
% 3.68/0.93  --bmc1_pre_inst_next_state              false
% 3.68/0.93  --bmc1_pre_inst_state                   false
% 3.68/0.93  --bmc1_pre_inst_reach_state             false
% 3.68/0.93  --bmc1_out_unsat_core                   false
% 3.68/0.93  --bmc1_aig_witness_out                  false
% 3.68/0.93  --bmc1_verbose                          false
% 3.68/0.93  --bmc1_dump_clauses_tptp                false
% 3.68/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.93  --bmc1_dump_file                        -
% 3.68/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.93  --bmc1_ucm_extend_mode                  1
% 3.68/0.93  --bmc1_ucm_init_mode                    2
% 3.68/0.93  --bmc1_ucm_cone_mode                    none
% 3.68/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.93  --bmc1_ucm_relax_model                  4
% 3.68/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.93  --bmc1_ucm_layered_model                none
% 3.68/0.93  --bmc1_ucm_max_lemma_size               10
% 3.68/0.93  
% 3.68/0.93  ------ AIG Options
% 3.68/0.93  
% 3.68/0.93  --aig_mode                              false
% 3.68/0.93  
% 3.68/0.93  ------ Instantiation Options
% 3.68/0.93  
% 3.68/0.93  --instantiation_flag                    true
% 3.68/0.93  --inst_sos_flag                         true
% 3.68/0.93  --inst_sos_phase                        true
% 3.68/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.93  --inst_lit_sel_side                     num_symb
% 3.68/0.93  --inst_solver_per_active                1400
% 3.68/0.93  --inst_solver_calls_frac                1.
% 3.68/0.93  --inst_passive_queue_type               priority_queues
% 3.68/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.93  --inst_passive_queues_freq              [25;2]
% 3.68/0.93  --inst_dismatching                      true
% 3.68/0.93  --inst_eager_unprocessed_to_passive     true
% 3.68/0.93  --inst_prop_sim_given                   true
% 3.68/0.93  --inst_prop_sim_new                     false
% 3.68/0.93  --inst_subs_new                         false
% 3.68/0.93  --inst_eq_res_simp                      false
% 3.68/0.93  --inst_subs_given                       false
% 3.68/0.93  --inst_orphan_elimination               true
% 3.68/0.93  --inst_learning_loop_flag               true
% 3.68/0.93  --inst_learning_start                   3000
% 3.68/0.93  --inst_learning_factor                  2
% 3.68/0.93  --inst_start_prop_sim_after_learn       3
% 3.68/0.93  --inst_sel_renew                        solver
% 3.68/0.93  --inst_lit_activity_flag                true
% 3.68/0.93  --inst_restr_to_given                   false
% 3.68/0.93  --inst_activity_threshold               500
% 3.68/0.93  --inst_out_proof                        true
% 3.68/0.93  
% 3.68/0.93  ------ Resolution Options
% 3.68/0.93  
% 3.68/0.93  --resolution_flag                       true
% 3.68/0.93  --res_lit_sel                           adaptive
% 3.68/0.93  --res_lit_sel_side                      none
% 3.68/0.93  --res_ordering                          kbo
% 3.68/0.93  --res_to_prop_solver                    active
% 3.68/0.93  --res_prop_simpl_new                    false
% 3.68/0.93  --res_prop_simpl_given                  true
% 3.68/0.93  --res_passive_queue_type                priority_queues
% 3.68/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.93  --res_passive_queues_freq               [15;5]
% 3.68/0.93  --res_forward_subs                      full
% 3.68/0.93  --res_backward_subs                     full
% 3.68/0.93  --res_forward_subs_resolution           true
% 3.68/0.93  --res_backward_subs_resolution          true
% 3.68/0.93  --res_orphan_elimination                true
% 3.68/0.93  --res_time_limit                        2.
% 3.68/0.93  --res_out_proof                         true
% 3.68/0.93  
% 3.68/0.93  ------ Superposition Options
% 3.68/0.93  
% 3.68/0.93  --superposition_flag                    true
% 3.68/0.93  --sup_passive_queue_type                priority_queues
% 3.68/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.93  --demod_completeness_check              fast
% 3.68/0.93  --demod_use_ground                      true
% 3.68/0.93  --sup_to_prop_solver                    passive
% 3.68/0.93  --sup_prop_simpl_new                    true
% 3.68/0.93  --sup_prop_simpl_given                  true
% 3.68/0.93  --sup_fun_splitting                     true
% 3.68/0.93  --sup_smt_interval                      50000
% 3.68/0.93  
% 3.68/0.93  ------ Superposition Simplification Setup
% 3.68/0.93  
% 3.68/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.93  --sup_immed_triv                        [TrivRules]
% 3.68/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.93  --sup_immed_bw_main                     []
% 3.68/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.93  --sup_input_bw                          []
% 3.68/0.93  
% 3.68/0.93  ------ Combination Options
% 3.68/0.93  
% 3.68/0.93  --comb_res_mult                         3
% 3.68/0.93  --comb_sup_mult                         2
% 3.68/0.93  --comb_inst_mult                        10
% 3.68/0.93  
% 3.68/0.93  ------ Debug Options
% 3.68/0.93  
% 3.68/0.93  --dbg_backtrace                         false
% 3.68/0.93  --dbg_dump_prop_clauses                 false
% 3.68/0.93  --dbg_dump_prop_clauses_file            -
% 3.68/0.93  --dbg_out_stat                          false
% 3.68/0.93  ------ Parsing...
% 3.68/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.93  
% 3.68/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.68/0.93  
% 3.68/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.93  
% 3.68/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.93  ------ Proving...
% 3.68/0.93  ------ Problem Properties 
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  clauses                                 18
% 3.68/0.93  conjectures                             3
% 3.68/0.93  EPR                                     3
% 3.68/0.93  Horn                                    15
% 3.68/0.93  unary                                   11
% 3.68/0.93  binary                                  1
% 3.68/0.93  lits                                    36
% 3.68/0.93  lits eq                                 20
% 3.68/0.93  fd_pure                                 0
% 3.68/0.93  fd_pseudo                               0
% 3.68/0.93  fd_cond                                 0
% 3.68/0.93  fd_pseudo_cond                          6
% 3.68/0.93  AC symbols                              0
% 3.68/0.93  
% 3.68/0.93  ------ Schedule dynamic 5 is on 
% 3.68/0.93  
% 3.68/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  ------ 
% 3.68/0.93  Current options:
% 3.68/0.93  ------ 
% 3.68/0.93  
% 3.68/0.93  ------ Input Options
% 3.68/0.93  
% 3.68/0.93  --out_options                           all
% 3.68/0.93  --tptp_safe_out                         true
% 3.68/0.93  --problem_path                          ""
% 3.68/0.93  --include_path                          ""
% 3.68/0.93  --clausifier                            res/vclausify_rel
% 3.68/0.93  --clausifier_options                    ""
% 3.68/0.93  --stdin                                 false
% 3.68/0.93  --stats_out                             all
% 3.68/0.93  
% 3.68/0.93  ------ General Options
% 3.68/0.93  
% 3.68/0.93  --fof                                   false
% 3.68/0.93  --time_out_real                         305.
% 3.68/0.93  --time_out_virtual                      -1.
% 3.68/0.93  --symbol_type_check                     false
% 3.68/0.93  --clausify_out                          false
% 3.68/0.93  --sig_cnt_out                           false
% 3.68/0.93  --trig_cnt_out                          false
% 3.68/0.93  --trig_cnt_out_tolerance                1.
% 3.68/0.93  --trig_cnt_out_sk_spl                   false
% 3.68/0.93  --abstr_cl_out                          false
% 3.68/0.93  
% 3.68/0.93  ------ Global Options
% 3.68/0.93  
% 3.68/0.93  --schedule                              default
% 3.68/0.93  --add_important_lit                     false
% 3.68/0.93  --prop_solver_per_cl                    1000
% 3.68/0.93  --min_unsat_core                        false
% 3.68/0.93  --soft_assumptions                      false
% 3.68/0.93  --soft_lemma_size                       3
% 3.68/0.93  --prop_impl_unit_size                   0
% 3.68/0.93  --prop_impl_unit                        []
% 3.68/0.93  --share_sel_clauses                     true
% 3.68/0.93  --reset_solvers                         false
% 3.68/0.93  --bc_imp_inh                            [conj_cone]
% 3.68/0.93  --conj_cone_tolerance                   3.
% 3.68/0.93  --extra_neg_conj                        none
% 3.68/0.93  --large_theory_mode                     true
% 3.68/0.93  --prolific_symb_bound                   200
% 3.68/0.93  --lt_threshold                          2000
% 3.68/0.93  --clause_weak_htbl                      true
% 3.68/0.93  --gc_record_bc_elim                     false
% 3.68/0.93  
% 3.68/0.93  ------ Preprocessing Options
% 3.68/0.93  
% 3.68/0.93  --preprocessing_flag                    true
% 3.68/0.93  --time_out_prep_mult                    0.1
% 3.68/0.93  --splitting_mode                        input
% 3.68/0.93  --splitting_grd                         true
% 3.68/0.93  --splitting_cvd                         false
% 3.68/0.93  --splitting_cvd_svl                     false
% 3.68/0.93  --splitting_nvd                         32
% 3.68/0.93  --sub_typing                            true
% 3.68/0.93  --prep_gs_sim                           true
% 3.68/0.93  --prep_unflatten                        true
% 3.68/0.93  --prep_res_sim                          true
% 3.68/0.93  --prep_upred                            true
% 3.68/0.93  --prep_sem_filter                       exhaustive
% 3.68/0.93  --prep_sem_filter_out                   false
% 3.68/0.93  --pred_elim                             true
% 3.68/0.93  --res_sim_input                         true
% 3.68/0.93  --eq_ax_congr_red                       true
% 3.68/0.93  --pure_diseq_elim                       true
% 3.68/0.93  --brand_transform                       false
% 3.68/0.93  --non_eq_to_eq                          false
% 3.68/0.93  --prep_def_merge                        true
% 3.68/0.93  --prep_def_merge_prop_impl              false
% 3.68/0.93  --prep_def_merge_mbd                    true
% 3.68/0.93  --prep_def_merge_tr_red                 false
% 3.68/0.93  --prep_def_merge_tr_cl                  false
% 3.68/0.93  --smt_preprocessing                     true
% 3.68/0.93  --smt_ac_axioms                         fast
% 3.68/0.93  --preprocessed_out                      false
% 3.68/0.93  --preprocessed_stats                    false
% 3.68/0.93  
% 3.68/0.93  ------ Abstraction refinement Options
% 3.68/0.93  
% 3.68/0.93  --abstr_ref                             []
% 3.68/0.93  --abstr_ref_prep                        false
% 3.68/0.93  --abstr_ref_until_sat                   false
% 3.68/0.93  --abstr_ref_sig_restrict                funpre
% 3.68/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.93  --abstr_ref_under                       []
% 3.68/0.93  
% 3.68/0.93  ------ SAT Options
% 3.68/0.93  
% 3.68/0.93  --sat_mode                              false
% 3.68/0.93  --sat_fm_restart_options                ""
% 3.68/0.93  --sat_gr_def                            false
% 3.68/0.93  --sat_epr_types                         true
% 3.68/0.93  --sat_non_cyclic_types                  false
% 3.68/0.93  --sat_finite_models                     false
% 3.68/0.93  --sat_fm_lemmas                         false
% 3.68/0.93  --sat_fm_prep                           false
% 3.68/0.93  --sat_fm_uc_incr                        true
% 3.68/0.93  --sat_out_model                         small
% 3.68/0.93  --sat_out_clauses                       false
% 3.68/0.93  
% 3.68/0.93  ------ QBF Options
% 3.68/0.93  
% 3.68/0.93  --qbf_mode                              false
% 3.68/0.93  --qbf_elim_univ                         false
% 3.68/0.93  --qbf_dom_inst                          none
% 3.68/0.93  --qbf_dom_pre_inst                      false
% 3.68/0.93  --qbf_sk_in                             false
% 3.68/0.93  --qbf_pred_elim                         true
% 3.68/0.93  --qbf_split                             512
% 3.68/0.93  
% 3.68/0.93  ------ BMC1 Options
% 3.68/0.93  
% 3.68/0.93  --bmc1_incremental                      false
% 3.68/0.93  --bmc1_axioms                           reachable_all
% 3.68/0.93  --bmc1_min_bound                        0
% 3.68/0.93  --bmc1_max_bound                        -1
% 3.68/0.93  --bmc1_max_bound_default                -1
% 3.68/0.93  --bmc1_symbol_reachability              true
% 3.68/0.93  --bmc1_property_lemmas                  false
% 3.68/0.93  --bmc1_k_induction                      false
% 3.68/0.93  --bmc1_non_equiv_states                 false
% 3.68/0.93  --bmc1_deadlock                         false
% 3.68/0.93  --bmc1_ucm                              false
% 3.68/0.93  --bmc1_add_unsat_core                   none
% 3.68/0.93  --bmc1_unsat_core_children              false
% 3.68/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.93  --bmc1_out_stat                         full
% 3.68/0.93  --bmc1_ground_init                      false
% 3.68/0.93  --bmc1_pre_inst_next_state              false
% 3.68/0.93  --bmc1_pre_inst_state                   false
% 3.68/0.93  --bmc1_pre_inst_reach_state             false
% 3.68/0.93  --bmc1_out_unsat_core                   false
% 3.68/0.93  --bmc1_aig_witness_out                  false
% 3.68/0.93  --bmc1_verbose                          false
% 3.68/0.93  --bmc1_dump_clauses_tptp                false
% 3.68/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.93  --bmc1_dump_file                        -
% 3.68/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.93  --bmc1_ucm_extend_mode                  1
% 3.68/0.93  --bmc1_ucm_init_mode                    2
% 3.68/0.93  --bmc1_ucm_cone_mode                    none
% 3.68/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.93  --bmc1_ucm_relax_model                  4
% 3.68/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.93  --bmc1_ucm_layered_model                none
% 3.68/0.93  --bmc1_ucm_max_lemma_size               10
% 3.68/0.93  
% 3.68/0.93  ------ AIG Options
% 3.68/0.93  
% 3.68/0.93  --aig_mode                              false
% 3.68/0.93  
% 3.68/0.93  ------ Instantiation Options
% 3.68/0.93  
% 3.68/0.93  --instantiation_flag                    true
% 3.68/0.93  --inst_sos_flag                         true
% 3.68/0.93  --inst_sos_phase                        true
% 3.68/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.93  --inst_lit_sel_side                     none
% 3.68/0.93  --inst_solver_per_active                1400
% 3.68/0.93  --inst_solver_calls_frac                1.
% 3.68/0.93  --inst_passive_queue_type               priority_queues
% 3.68/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.93  --inst_passive_queues_freq              [25;2]
% 3.68/0.93  --inst_dismatching                      true
% 3.68/0.93  --inst_eager_unprocessed_to_passive     true
% 3.68/0.93  --inst_prop_sim_given                   true
% 3.68/0.93  --inst_prop_sim_new                     false
% 3.68/0.93  --inst_subs_new                         false
% 3.68/0.93  --inst_eq_res_simp                      false
% 3.68/0.93  --inst_subs_given                       false
% 3.68/0.93  --inst_orphan_elimination               true
% 3.68/0.93  --inst_learning_loop_flag               true
% 3.68/0.93  --inst_learning_start                   3000
% 3.68/0.93  --inst_learning_factor                  2
% 3.68/0.93  --inst_start_prop_sim_after_learn       3
% 3.68/0.93  --inst_sel_renew                        solver
% 3.68/0.93  --inst_lit_activity_flag                true
% 3.68/0.93  --inst_restr_to_given                   false
% 3.68/0.93  --inst_activity_threshold               500
% 3.68/0.93  --inst_out_proof                        true
% 3.68/0.93  
% 3.68/0.93  ------ Resolution Options
% 3.68/0.93  
% 3.68/0.93  --resolution_flag                       false
% 3.68/0.93  --res_lit_sel                           adaptive
% 3.68/0.93  --res_lit_sel_side                      none
% 3.68/0.93  --res_ordering                          kbo
% 3.68/0.93  --res_to_prop_solver                    active
% 3.68/0.93  --res_prop_simpl_new                    false
% 3.68/0.93  --res_prop_simpl_given                  true
% 3.68/0.93  --res_passive_queue_type                priority_queues
% 3.68/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.93  --res_passive_queues_freq               [15;5]
% 3.68/0.93  --res_forward_subs                      full
% 3.68/0.93  --res_backward_subs                     full
% 3.68/0.93  --res_forward_subs_resolution           true
% 3.68/0.93  --res_backward_subs_resolution          true
% 3.68/0.93  --res_orphan_elimination                true
% 3.68/0.93  --res_time_limit                        2.
% 3.68/0.93  --res_out_proof                         true
% 3.68/0.93  
% 3.68/0.93  ------ Superposition Options
% 3.68/0.93  
% 3.68/0.93  --superposition_flag                    true
% 3.68/0.93  --sup_passive_queue_type                priority_queues
% 3.68/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.93  --demod_completeness_check              fast
% 3.68/0.93  --demod_use_ground                      true
% 3.68/0.93  --sup_to_prop_solver                    passive
% 3.68/0.93  --sup_prop_simpl_new                    true
% 3.68/0.93  --sup_prop_simpl_given                  true
% 3.68/0.93  --sup_fun_splitting                     true
% 3.68/0.93  --sup_smt_interval                      50000
% 3.68/0.93  
% 3.68/0.93  ------ Superposition Simplification Setup
% 3.68/0.93  
% 3.68/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.93  --sup_immed_triv                        [TrivRules]
% 3.68/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.93  --sup_immed_bw_main                     []
% 3.68/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.93  --sup_input_bw                          []
% 3.68/0.93  
% 3.68/0.93  ------ Combination Options
% 3.68/0.93  
% 3.68/0.93  --comb_res_mult                         3
% 3.68/0.93  --comb_sup_mult                         2
% 3.68/0.93  --comb_inst_mult                        10
% 3.68/0.93  
% 3.68/0.93  ------ Debug Options
% 3.68/0.93  
% 3.68/0.93  --dbg_backtrace                         false
% 3.68/0.93  --dbg_dump_prop_clauses                 false
% 3.68/0.93  --dbg_dump_prop_clauses_file            -
% 3.68/0.93  --dbg_out_stat                          false
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  ------ Proving...
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  % SZS status Theorem for theBenchmark.p
% 3.68/0.93  
% 3.68/0.93   Resolution empty clause
% 3.68/0.93  
% 3.68/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.93  
% 3.68/0.93  fof(f1,axiom,(
% 3.68/0.93    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f24,plain,(
% 3.68/0.93    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.68/0.93    inference(cnf_transformation,[],[f1])).
% 3.68/0.93  
% 3.68/0.93  fof(f2,axiom,(
% 3.68/0.93    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f11,plain,(
% 3.68/0.93    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.68/0.93    inference(ennf_transformation,[],[f2])).
% 3.68/0.93  
% 3.68/0.93  fof(f15,plain,(
% 3.68/0.93    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.93    inference(nnf_transformation,[],[f11])).
% 3.68/0.93  
% 3.68/0.93  fof(f16,plain,(
% 3.68/0.93    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.93    inference(flattening,[],[f15])).
% 3.68/0.93  
% 3.68/0.93  fof(f17,plain,(
% 3.68/0.93    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.93    inference(rectify,[],[f16])).
% 3.68/0.93  
% 3.68/0.93  fof(f18,plain,(
% 3.68/0.93    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.68/0.93    introduced(choice_axiom,[])).
% 3.68/0.93  
% 3.68/0.93  fof(f19,plain,(
% 3.68/0.93    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.68/0.93  
% 3.68/0.93  fof(f27,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.68/0.93    inference(cnf_transformation,[],[f19])).
% 3.68/0.93  
% 3.68/0.93  fof(f5,axiom,(
% 3.68/0.93    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f35,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.68/0.93    inference(cnf_transformation,[],[f5])).
% 3.68/0.93  
% 3.68/0.93  fof(f6,axiom,(
% 3.68/0.93    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f36,plain,(
% 3.68/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.68/0.93    inference(cnf_transformation,[],[f6])).
% 3.68/0.93  
% 3.68/0.93  fof(f46,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.68/0.93    inference(definition_unfolding,[],[f35,f36])).
% 3.68/0.93  
% 3.68/0.93  fof(f54,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.68/0.93    inference(definition_unfolding,[],[f27,f46])).
% 3.68/0.93  
% 3.68/0.93  fof(f66,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X5,X2) != X3) )),
% 3.68/0.93    inference(equality_resolution,[],[f54])).
% 3.68/0.93  
% 3.68/0.93  fof(f67,plain,(
% 3.68/0.93    ( ! [X2,X0,X5] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2))) )),
% 3.68/0.93    inference(equality_resolution,[],[f66])).
% 3.68/0.93  
% 3.68/0.93  fof(f28,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.68/0.93    inference(cnf_transformation,[],[f19])).
% 3.68/0.93  
% 3.68/0.93  fof(f53,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.68/0.93    inference(definition_unfolding,[],[f28,f46])).
% 3.68/0.93  
% 3.68/0.93  fof(f64,plain,(
% 3.68/0.93    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 3.68/0.93    inference(equality_resolution,[],[f53])).
% 3.68/0.93  
% 3.68/0.93  fof(f65,plain,(
% 3.68/0.93    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 3.68/0.93    inference(equality_resolution,[],[f64])).
% 3.68/0.93  
% 3.68/0.93  fof(f9,conjecture,(
% 3.68/0.93    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f10,negated_conjecture,(
% 3.68/0.93    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.68/0.93    inference(negated_conjecture,[],[f9])).
% 3.68/0.93  
% 3.68/0.93  fof(f14,plain,(
% 3.68/0.93    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.68/0.93    inference(ennf_transformation,[],[f10])).
% 3.68/0.93  
% 3.68/0.93  fof(f22,plain,(
% 3.68/0.93    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 3.68/0.93    introduced(choice_axiom,[])).
% 3.68/0.93  
% 3.68/0.93  fof(f23,plain,(
% 3.68/0.93    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.68/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f22])).
% 3.68/0.93  
% 3.68/0.93  fof(f43,plain,(
% 3.68/0.93    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.68/0.93    inference(cnf_transformation,[],[f23])).
% 3.68/0.93  
% 3.68/0.93  fof(f4,axiom,(
% 3.68/0.93    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f34,plain,(
% 3.68/0.93    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.68/0.93    inference(cnf_transformation,[],[f4])).
% 3.68/0.93  
% 3.68/0.93  fof(f47,plain,(
% 3.68/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.68/0.93    inference(definition_unfolding,[],[f34,f46])).
% 3.68/0.93  
% 3.68/0.93  fof(f63,plain,(
% 3.68/0.93    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK4))),
% 3.68/0.93    inference(definition_unfolding,[],[f43,f47,f47])).
% 3.68/0.93  
% 3.68/0.93  fof(f7,axiom,(
% 3.68/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f12,plain,(
% 3.68/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.68/0.93    inference(ennf_transformation,[],[f7])).
% 3.68/0.93  
% 3.68/0.93  fof(f20,plain,(
% 3.68/0.93    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.68/0.93    inference(nnf_transformation,[],[f12])).
% 3.68/0.93  
% 3.68/0.93  fof(f21,plain,(
% 3.68/0.93    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.68/0.93    inference(flattening,[],[f20])).
% 3.68/0.93  
% 3.68/0.93  fof(f37,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.68/0.93    inference(cnf_transformation,[],[f21])).
% 3.68/0.93  
% 3.68/0.93  fof(f3,axiom,(
% 3.68/0.93    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f33,plain,(
% 3.68/0.93    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.68/0.93    inference(cnf_transformation,[],[f3])).
% 3.68/0.93  
% 3.68/0.93  fof(f48,plain,(
% 3.68/0.93    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.68/0.93    inference(definition_unfolding,[],[f33,f47])).
% 3.68/0.93  
% 3.68/0.93  fof(f61,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (k3_enumset1(X1,X1,X1,X1,X2) = X0 | k3_enumset1(X2,X2,X2,X2,X2) = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))) )),
% 3.68/0.93    inference(definition_unfolding,[],[f37,f47,f48,f48,f47])).
% 3.68/0.93  
% 3.68/0.93  fof(f25,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.68/0.93    inference(cnf_transformation,[],[f19])).
% 3.68/0.93  
% 3.68/0.93  fof(f56,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.68/0.93    inference(definition_unfolding,[],[f25,f46])).
% 3.68/0.93  
% 3.68/0.93  fof(f70,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.68/0.93    inference(equality_resolution,[],[f56])).
% 3.68/0.93  
% 3.68/0.93  fof(f44,plain,(
% 3.68/0.93    sK1 != sK3),
% 3.68/0.93    inference(cnf_transformation,[],[f23])).
% 3.68/0.93  
% 3.68/0.93  fof(f8,axiom,(
% 3.68/0.93    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 3.68/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.93  
% 3.68/0.93  fof(f13,plain,(
% 3.68/0.93    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 3.68/0.93    inference(ennf_transformation,[],[f8])).
% 3.68/0.93  
% 3.68/0.93  fof(f42,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.68/0.93    inference(cnf_transformation,[],[f13])).
% 3.68/0.93  
% 3.68/0.93  fof(f62,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (X0 = X2 | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 3.68/0.93    inference(definition_unfolding,[],[f42,f47,f48])).
% 3.68/0.93  
% 3.68/0.93  fof(f39,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.68/0.93    inference(cnf_transformation,[],[f21])).
% 3.68/0.93  
% 3.68/0.93  fof(f59,plain,(
% 3.68/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X1,X1,X1,X1,X1) != X0) )),
% 3.68/0.93    inference(definition_unfolding,[],[f39,f47,f48])).
% 3.68/0.93  
% 3.68/0.93  fof(f73,plain,(
% 3.68/0.93    ( ! [X2,X1] : (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 3.68/0.93    inference(equality_resolution,[],[f59])).
% 3.68/0.93  
% 3.68/0.93  fof(f45,plain,(
% 3.68/0.93    sK1 != sK4),
% 3.68/0.93    inference(cnf_transformation,[],[f23])).
% 3.68/0.93  
% 3.68/0.93  fof(f26,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.68/0.93    inference(cnf_transformation,[],[f19])).
% 3.68/0.93  
% 3.68/0.93  fof(f55,plain,(
% 3.68/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.68/0.93    inference(definition_unfolding,[],[f26,f46])).
% 3.68/0.93  
% 3.68/0.93  fof(f68,plain,(
% 3.68/0.93    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.68/0.93    inference(equality_resolution,[],[f55])).
% 3.68/0.93  
% 3.68/0.93  fof(f69,plain,(
% 3.68/0.93    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.68/0.93    inference(equality_resolution,[],[f68])).
% 3.68/0.93  
% 3.68/0.93  cnf(c_0,plain,
% 3.68/0.93      ( r1_tarski(k1_xboole_0,X0) ),
% 3.68/0.93      inference(cnf_transformation,[],[f24]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_786,plain,
% 3.68/0.93      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6,plain,
% 3.68/0.93      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) ),
% 3.68/0.93      inference(cnf_transformation,[],[f67]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_780,plain,
% 3.68/0.93      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) = iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_5,plain,
% 3.68/0.93      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 3.68/0.93      inference(cnf_transformation,[],[f65]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_781,plain,
% 3.68/0.93      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_17,negated_conjecture,
% 3.68/0.93      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
% 3.68/0.93      inference(cnf_transformation,[],[f63]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_771,plain,
% 3.68/0.93      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_13,plain,
% 3.68/0.93      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
% 3.68/0.93      | k3_enumset1(X1,X1,X1,X1,X2) = X0
% 3.68/0.93      | k3_enumset1(X2,X2,X2,X2,X2) = X0
% 3.68/0.93      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 3.68/0.93      | k1_xboole_0 = X0 ),
% 3.68/0.93      inference(cnf_transformation,[],[f61]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_773,plain,
% 3.68/0.93      ( k3_enumset1(X0,X0,X0,X0,X1) = X2
% 3.68/0.93      | k3_enumset1(X1,X1,X1,X1,X1) = X2
% 3.68/0.93      | k3_enumset1(X0,X0,X0,X0,X0) = X2
% 3.68/0.93      | k1_xboole_0 = X2
% 3.68/0.93      | r1_tarski(X2,k3_enumset1(X0,X0,X0,X0,X1)) != iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_1977,plain,
% 3.68/0.93      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_771,c_773]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_8,plain,
% 3.68/0.93      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.68/0.93      | X0 = X1
% 3.68/0.93      | X0 = X2
% 3.68/0.93      | X0 = X3 ),
% 3.68/0.93      inference(cnf_transformation,[],[f70]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_778,plain,
% 3.68/0.93      ( X0 = X1
% 3.68/0.93      | X0 = X2
% 3.68/0.93      | X0 = X3
% 3.68/0.93      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2034,plain,
% 3.68/0.93      ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK3 = X0
% 3.68/0.93      | r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_1977,c_778]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2135,plain,
% 3.68/0.93      ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK2 = sK3 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_781,c_2034]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_16,negated_conjecture,
% 3.68/0.93      ( sK1 != sK3 ),
% 3.68/0.93      inference(cnf_transformation,[],[f44]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_14,plain,
% 3.68/0.93      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))
% 3.68/0.93      | X2 = X0 ),
% 3.68/0.93      inference(cnf_transformation,[],[f62]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_20,plain,
% 3.68/0.93      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 3.68/0.93      | sK1 = sK1 ),
% 3.68/0.93      inference(instantiation,[status(thm)],[c_14]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_11,plain,
% 3.68/0.93      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.68/0.93      inference(cnf_transformation,[],[f73]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_29,plain,
% 3.68/0.93      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.68/0.93      inference(instantiation,[status(thm)],[c_11]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_527,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_817,plain,
% 3.68/0.93      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 3.68/0.93      inference(instantiation,[status(thm)],[c_527]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_818,plain,
% 3.68/0.93      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 3.68/0.93      inference(instantiation,[status(thm)],[c_817]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2136,plain,
% 3.68/0.93      ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK3 = sK1 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_780,c_2034]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2264,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
% 3.68/0.93      inference(global_propositional_subsumption,
% 3.68/0.93                [status(thm)],
% 3.68/0.93                [c_2135,c_16,c_20,c_29,c_818,c_2136]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2265,plain,
% 3.68/0.93      ( k3_enumset1(sK3,sK3,sK3,sK3,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.68/0.93      inference(renaming,[status(thm)],[c_2264]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2267,plain,
% 3.68/0.93      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | r2_hidden(sK4,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_2265,c_781]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2291,plain,
% 3.68/0.93      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK2 = sK4
% 3.68/0.93      | sK4 = sK1 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_2267,c_778]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_15,negated_conjecture,
% 3.68/0.93      ( sK1 != sK4 ),
% 3.68/0.93      inference(cnf_transformation,[],[f45]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_807,plain,
% 3.68/0.93      ( sK4 != X0 | sK1 != X0 | sK1 = sK4 ),
% 3.68/0.93      inference(instantiation,[status(thm)],[c_527]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_808,plain,
% 3.68/0.93      ( sK4 != sK1 | sK1 = sK4 | sK1 != sK1 ),
% 3.68/0.93      inference(instantiation,[status(thm)],[c_807]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2470,plain,
% 3.68/0.93      ( sK2 = sK4
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
% 3.68/0.93      inference(global_propositional_subsumption,
% 3.68/0.93                [status(thm)],
% 3.68/0.93                [c_2291,c_15,c_20,c_29,c_808]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2471,plain,
% 3.68/0.93      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK2 = sK4 ),
% 3.68/0.93      inference(renaming,[status(thm)],[c_2470]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_7,plain,
% 3.68/0.93      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.68/0.93      inference(cnf_transformation,[],[f69]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_779,plain,
% 3.68/0.93      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2472,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK2 = sK4
% 3.68/0.93      | r2_hidden(sK4,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_2471,c_779]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2506,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.68/0.93      | sK2 = sK4
% 3.68/0.93      | sK4 = sK1 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_2472,c_778]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2884,plain,
% 3.68/0.93      ( sK2 = sK4 | k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.68/0.93      inference(global_propositional_subsumption,
% 3.68/0.93                [status(thm)],
% 3.68/0.93                [c_2506,c_15,c_20,c_29,c_808]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2885,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 | sK2 = sK4 ),
% 3.68/0.93      inference(renaming,[status(thm)],[c_2884]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_772,plain,
% 3.68/0.93      ( X0 = X1
% 3.68/0.93      | r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.68/0.93      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_2899,plain,
% 3.68/0.93      ( sK2 = sK4
% 3.68/0.93      | sK1 = X0
% 3.68/0.93      | r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_2885,c_772]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_4859,plain,
% 3.68/0.93      ( sK2 = sK4 | sK1 = X0 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_786,c_2899]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_5019,plain,
% 3.68/0.93      ( sK2 = sK4 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_4859,c_15]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_5089,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK4)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 ),
% 3.68/0.93      inference(demodulation,[status(thm)],[c_5019,c_2265]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_5311,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
% 3.68/0.93      | sK3 = X0
% 3.68/0.93      | r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK4),k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_5089,c_772]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_5310,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
% 3.68/0.93      | sK3 = X0
% 3.68/0.93      | sK4 = X0
% 3.68/0.93      | r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK4)) != iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_5089,c_778]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6199,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
% 3.68/0.93      | sK3 = sK1
% 3.68/0.93      | sK4 = sK1 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_780,c_5310]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6208,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 3.68/0.93      | k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 ),
% 3.68/0.93      inference(global_propositional_subsumption,
% 3.68/0.93                [status(thm)],
% 3.68/0.93                [c_5311,c_16,c_15,c_20,c_29,c_808,c_818,c_6199]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6226,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0
% 3.68/0.93      | sK4 = X0
% 3.68/0.93      | r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK4)) != iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_6208,c_778]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6774,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 | sK4 = sK1 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_780,c_6226]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6781,plain,
% 3.68/0.93      ( k3_enumset1(sK1,sK1,sK1,sK1,sK4) = k1_xboole_0 ),
% 3.68/0.93      inference(global_propositional_subsumption,
% 3.68/0.93                [status(thm)],
% 3.68/0.93                [c_6774,c_15,c_20,c_29,c_808]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_6805,plain,
% 3.68/0.93      ( sK1 = X0
% 3.68/0.93      | r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_6781,c_772]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_7319,plain,
% 3.68/0.93      ( sK1 = X0 ),
% 3.68/0.93      inference(superposition,[status(thm)],[c_786,c_6805]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_7359,plain,
% 3.68/0.93      ( sK1 != sK1 ),
% 3.68/0.93      inference(demodulation,[status(thm)],[c_7319,c_15]) ).
% 3.68/0.93  
% 3.68/0.93  cnf(c_7362,plain,
% 3.68/0.93      ( $false ),
% 3.68/0.93      inference(equality_resolution_simp,[status(thm)],[c_7359]) ).
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.93  
% 3.68/0.93  ------                               Statistics
% 3.68/0.93  
% 3.68/0.93  ------ General
% 3.68/0.93  
% 3.68/0.93  abstr_ref_over_cycles:                  0
% 3.68/0.93  abstr_ref_under_cycles:                 0
% 3.68/0.93  gc_basic_clause_elim:                   0
% 3.68/0.93  forced_gc_time:                         0
% 3.68/0.93  parsing_time:                           0.013
% 3.68/0.93  unif_index_cands_time:                  0.
% 3.68/0.93  unif_index_add_time:                    0.
% 3.68/0.93  orderings_time:                         0.
% 3.68/0.93  out_proof_time:                         0.014
% 3.68/0.93  total_time:                             0.348
% 3.68/0.93  num_of_symbols:                         37
% 3.68/0.93  num_of_terms:                           8251
% 3.68/0.93  
% 3.68/0.93  ------ Preprocessing
% 3.68/0.93  
% 3.68/0.93  num_of_splits:                          0
% 3.68/0.93  num_of_split_atoms:                     0
% 3.68/0.93  num_of_reused_defs:                     0
% 3.68/0.93  num_eq_ax_congr_red:                    8
% 3.68/0.93  num_of_sem_filtered_clauses:            1
% 3.68/0.93  num_of_subtypes:                        0
% 3.68/0.93  monotx_restored_types:                  0
% 3.68/0.93  sat_num_of_epr_types:                   0
% 3.68/0.93  sat_num_of_non_cyclic_types:            0
% 3.68/0.93  sat_guarded_non_collapsed_types:        0
% 3.68/0.93  num_pure_diseq_elim:                    0
% 3.68/0.93  simp_replaced_by:                       0
% 3.68/0.93  res_preprocessed:                       65
% 3.68/0.93  prep_upred:                             0
% 3.68/0.93  prep_unflattend:                        22
% 3.68/0.93  smt_new_axioms:                         0
% 3.68/0.93  pred_elim_cands:                        2
% 3.68/0.93  pred_elim:                              0
% 3.68/0.93  pred_elim_cl:                           0
% 3.68/0.93  pred_elim_cycles:                       2
% 3.68/0.93  merged_defs:                            0
% 3.68/0.93  merged_defs_ncl:                        0
% 3.68/0.93  bin_hyper_res:                          0
% 3.68/0.93  prep_cycles:                            3
% 3.68/0.93  pred_elim_time:                         0.005
% 3.68/0.93  splitting_time:                         0.
% 3.68/0.93  sem_filter_time:                        0.
% 3.68/0.93  monotx_time:                            0.001
% 3.68/0.93  subtype_inf_time:                       0.
% 3.68/0.93  
% 3.68/0.93  ------ Problem properties
% 3.68/0.93  
% 3.68/0.93  clauses:                                18
% 3.68/0.93  conjectures:                            3
% 3.68/0.93  epr:                                    3
% 3.68/0.93  horn:                                   15
% 3.68/0.93  ground:                                 3
% 3.68/0.93  unary:                                  11
% 3.68/0.93  binary:                                 1
% 3.68/0.93  lits:                                   36
% 3.68/0.93  lits_eq:                                20
% 3.68/0.93  fd_pure:                                0
% 3.68/0.93  fd_pseudo:                              0
% 3.68/0.93  fd_cond:                                0
% 3.68/0.93  fd_pseudo_cond:                         6
% 3.68/0.93  ac_symbols:                             0
% 3.68/0.93  
% 3.68/0.93  ------ Propositional Solver
% 3.68/0.93  
% 3.68/0.93  prop_solver_calls:                      24
% 3.68/0.93  prop_fast_solver_calls:                 758
% 3.68/0.93  smt_solver_calls:                       0
% 3.68/0.93  smt_fast_solver_calls:                  0
% 3.68/0.93  prop_num_of_clauses:                    2981
% 3.68/0.93  prop_preprocess_simplified:             6665
% 3.68/0.93  prop_fo_subsumed:                       78
% 3.68/0.93  prop_solver_time:                       0.
% 3.68/0.93  smt_solver_time:                        0.
% 3.68/0.93  smt_fast_solver_time:                   0.
% 3.68/0.93  prop_fast_solver_time:                  0.
% 3.68/0.93  prop_unsat_core_time:                   0.
% 3.68/0.93  
% 3.68/0.93  ------ QBF
% 3.68/0.93  
% 3.68/0.93  qbf_q_res:                              0
% 3.68/0.93  qbf_num_tautologies:                    0
% 3.68/0.93  qbf_prep_cycles:                        0
% 3.68/0.93  
% 3.68/0.93  ------ BMC1
% 3.68/0.93  
% 3.68/0.93  bmc1_current_bound:                     -1
% 3.68/0.93  bmc1_last_solved_bound:                 -1
% 3.68/0.93  bmc1_unsat_core_size:                   -1
% 3.68/0.93  bmc1_unsat_core_parents_size:           -1
% 3.68/0.93  bmc1_merge_next_fun:                    0
% 3.68/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.93  
% 3.68/0.93  ------ Instantiation
% 3.68/0.93  
% 3.68/0.93  inst_num_of_clauses:                    815
% 3.68/0.93  inst_num_in_passive:                    143
% 3.68/0.93  inst_num_in_active:                     278
% 3.68/0.93  inst_num_in_unprocessed:                398
% 3.68/0.93  inst_num_of_loops:                      310
% 3.68/0.93  inst_num_of_learning_restarts:          0
% 3.68/0.93  inst_num_moves_active_passive:          32
% 3.68/0.93  inst_lit_activity:                      0
% 3.68/0.93  inst_lit_activity_moves:                0
% 3.68/0.93  inst_num_tautologies:                   0
% 3.68/0.93  inst_num_prop_implied:                  0
% 3.68/0.93  inst_num_existing_simplified:           0
% 3.68/0.93  inst_num_eq_res_simplified:             0
% 3.68/0.93  inst_num_child_elim:                    0
% 3.68/0.93  inst_num_of_dismatching_blockings:      747
% 3.68/0.93  inst_num_of_non_proper_insts:           647
% 3.68/0.93  inst_num_of_duplicates:                 0
% 3.68/0.93  inst_inst_num_from_inst_to_res:         0
% 3.68/0.93  inst_dismatching_checking_time:         0.
% 3.68/0.93  
% 3.68/0.93  ------ Resolution
% 3.68/0.93  
% 3.68/0.93  res_num_of_clauses:                     0
% 3.68/0.93  res_num_in_passive:                     0
% 3.68/0.93  res_num_in_active:                      0
% 3.68/0.93  res_num_of_loops:                       68
% 3.68/0.93  res_forward_subset_subsumed:            108
% 3.68/0.93  res_backward_subset_subsumed:           8
% 3.68/0.93  res_forward_subsumed:                   1
% 3.68/0.93  res_backward_subsumed:                  0
% 3.68/0.93  res_forward_subsumption_resolution:     0
% 3.68/0.93  res_backward_subsumption_resolution:    0
% 3.68/0.93  res_clause_to_clause_subsumption:       3564
% 3.68/0.93  res_orphan_elimination:                 0
% 3.68/0.93  res_tautology_del:                      18
% 3.68/0.93  res_num_eq_res_simplified:              0
% 3.68/0.93  res_num_sel_changes:                    0
% 3.68/0.93  res_moves_from_active_to_pass:          0
% 3.68/0.93  
% 3.68/0.93  ------ Superposition
% 3.68/0.93  
% 3.68/0.93  sup_time_total:                         0.
% 3.68/0.93  sup_time_generating:                    0.
% 3.68/0.93  sup_time_sim_full:                      0.
% 3.68/0.93  sup_time_sim_immed:                     0.
% 3.68/0.93  
% 3.68/0.93  sup_num_of_clauses:                     209
% 3.68/0.93  sup_num_in_active:                      2
% 3.68/0.93  sup_num_in_passive:                     207
% 3.68/0.93  sup_num_of_loops:                       61
% 3.68/0.93  sup_fw_superposition:                   217
% 3.68/0.93  sup_bw_superposition:                   446
% 3.68/0.93  sup_immediate_simplified:               192
% 3.68/0.93  sup_given_eliminated:                   0
% 3.68/0.93  comparisons_done:                       0
% 3.68/0.93  comparisons_avoided:                    35
% 3.68/0.93  
% 3.68/0.93  ------ Simplifications
% 3.68/0.93  
% 3.68/0.93  
% 3.68/0.93  sim_fw_subset_subsumed:                 84
% 3.68/0.93  sim_bw_subset_subsumed:                 57
% 3.68/0.93  sim_fw_subsumed:                        68
% 3.68/0.93  sim_bw_subsumed:                        15
% 3.68/0.93  sim_fw_subsumption_res:                 0
% 3.68/0.93  sim_bw_subsumption_res:                 0
% 3.68/0.93  sim_tautology_del:                      2
% 3.68/0.93  sim_eq_tautology_del:                   34
% 3.68/0.93  sim_eq_res_simp:                        0
% 3.68/0.93  sim_fw_demodulated:                     8
% 3.68/0.93  sim_bw_demodulated:                     55
% 3.68/0.93  sim_light_normalised:                   8
% 3.68/0.93  sim_joinable_taut:                      0
% 3.68/0.93  sim_joinable_simp:                      0
% 3.68/0.93  sim_ac_normalised:                      0
% 3.68/0.93  sim_smt_subsumption:                    0
% 3.68/0.93  
%------------------------------------------------------------------------------
