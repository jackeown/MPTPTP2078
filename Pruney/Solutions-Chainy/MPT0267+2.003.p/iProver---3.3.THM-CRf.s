%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:29 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 382 expanded)
%              Number of clauses        :   62 ( 111 expanded)
%              Number of leaves         :   23 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          :  323 ( 823 expanded)
%              Number of equality atoms :  170 ( 450 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK2 = sK4
        | ~ r2_hidden(sK2,sK3)
        | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) )
      & ( ( sK2 != sK4
          & r2_hidden(sK2,sK3) )
        | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( sK2 = sK4
      | ~ r2_hidden(sK2,sK3)
      | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) )
    & ( ( sK2 != sK4
        & r2_hidden(sK2,sK3) )
      | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f33])).

fof(f61,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f73,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f61,f44,f67])).

fof(f59,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f59,f44,f67])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f76,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f71])).

fof(f77,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f76])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f78,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f60,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f60,f44,f67])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f47,f44])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_721,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ r2_hidden(sK2,sK3)
    | sK2 = sK4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_709,plain,
    ( sK2 = sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6632,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_709])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_707,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_719,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6592,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_719])).

cnf(c_7194,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | sK4 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6632,c_6592])).

cnf(c_7195,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7194])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_203,plain,
    ( X0 != X1
    | k3_xboole_0(X1,X2) != X3
    | k3_xboole_0(X3,X0) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_204,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_981,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_204])).

cnf(c_985,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_204,c_0])).

cnf(c_1166,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_981,c_985])).

cnf(c_1176,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1166,c_981])).

cnf(c_3123,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_981,c_1176])).

cnf(c_1145,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_981,c_0])).

cnf(c_983,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_204,c_204])).

cnf(c_989,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_983,c_204])).

cnf(c_1535,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_989])).

cnf(c_3184,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3123,c_1145,c_1535])).

cnf(c_3245,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3184,c_0])).

cnf(c_8,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_715,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1051,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_204,c_715])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_718,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4243,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),X1)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_718])).

cnf(c_11260,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_4243])).

cnf(c_11417,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_11260])).

cnf(c_11460,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7195,c_11417])).

cnf(c_434,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1033,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_14,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1618,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1619,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1618])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_876,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_1271,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1902,plain,
    ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1903,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2
    | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1902])).

cnf(c_440,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_9010,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_11755,plain,
    ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11460,c_1033,c_1619,c_1903,c_9010])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_710,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11762,plain,
    ( sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_11755,c_710])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_708,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12020,plain,
    ( sK2 != sK2
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11762,c_708])).

cnf(c_12021,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12020])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_714,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4239,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_718])).

cnf(c_13254,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12021,c_4239])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13254,c_1619])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.39/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.93  
% 3.39/0.93  ------  iProver source info
% 3.39/0.93  
% 3.39/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.93  git: non_committed_changes: false
% 3.39/0.93  git: last_make_outside_of_git: false
% 3.39/0.93  
% 3.39/0.93  ------ 
% 3.39/0.93  
% 3.39/0.93  ------ Input Options
% 3.39/0.93  
% 3.39/0.93  --out_options                           all
% 3.39/0.93  --tptp_safe_out                         true
% 3.39/0.93  --problem_path                          ""
% 3.39/0.93  --include_path                          ""
% 3.39/0.93  --clausifier                            res/vclausify_rel
% 3.39/0.93  --clausifier_options                    --mode clausify
% 3.39/0.93  --stdin                                 false
% 3.39/0.93  --stats_out                             all
% 3.39/0.93  
% 3.39/0.93  ------ General Options
% 3.39/0.93  
% 3.39/0.93  --fof                                   false
% 3.39/0.93  --time_out_real                         305.
% 3.39/0.93  --time_out_virtual                      -1.
% 3.39/0.93  --symbol_type_check                     false
% 3.39/0.93  --clausify_out                          false
% 3.39/0.93  --sig_cnt_out                           false
% 3.39/0.93  --trig_cnt_out                          false
% 3.39/0.93  --trig_cnt_out_tolerance                1.
% 3.39/0.93  --trig_cnt_out_sk_spl                   false
% 3.39/0.93  --abstr_cl_out                          false
% 3.39/0.93  
% 3.39/0.93  ------ Global Options
% 3.39/0.93  
% 3.39/0.93  --schedule                              default
% 3.39/0.93  --add_important_lit                     false
% 3.39/0.93  --prop_solver_per_cl                    1000
% 3.39/0.93  --min_unsat_core                        false
% 3.39/0.93  --soft_assumptions                      false
% 3.39/0.93  --soft_lemma_size                       3
% 3.39/0.93  --prop_impl_unit_size                   0
% 3.39/0.93  --prop_impl_unit                        []
% 3.39/0.93  --share_sel_clauses                     true
% 3.39/0.93  --reset_solvers                         false
% 3.39/0.93  --bc_imp_inh                            [conj_cone]
% 3.39/0.93  --conj_cone_tolerance                   3.
% 3.39/0.93  --extra_neg_conj                        none
% 3.39/0.93  --large_theory_mode                     true
% 3.39/0.93  --prolific_symb_bound                   200
% 3.39/0.93  --lt_threshold                          2000
% 3.39/0.93  --clause_weak_htbl                      true
% 3.39/0.93  --gc_record_bc_elim                     false
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing Options
% 3.39/0.93  
% 3.39/0.93  --preprocessing_flag                    true
% 3.39/0.93  --time_out_prep_mult                    0.1
% 3.39/0.93  --splitting_mode                        input
% 3.39/0.93  --splitting_grd                         true
% 3.39/0.93  --splitting_cvd                         false
% 3.39/0.93  --splitting_cvd_svl                     false
% 3.39/0.93  --splitting_nvd                         32
% 3.39/0.93  --sub_typing                            true
% 3.39/0.93  --prep_gs_sim                           true
% 3.39/0.93  --prep_unflatten                        true
% 3.39/0.93  --prep_res_sim                          true
% 3.39/0.93  --prep_upred                            true
% 3.39/0.93  --prep_sem_filter                       exhaustive
% 3.39/0.93  --prep_sem_filter_out                   false
% 3.39/0.93  --pred_elim                             true
% 3.39/0.93  --res_sim_input                         true
% 3.39/0.93  --eq_ax_congr_red                       true
% 3.39/0.93  --pure_diseq_elim                       true
% 3.39/0.93  --brand_transform                       false
% 3.39/0.93  --non_eq_to_eq                          false
% 3.39/0.93  --prep_def_merge                        true
% 3.39/0.93  --prep_def_merge_prop_impl              false
% 3.39/0.93  --prep_def_merge_mbd                    true
% 3.39/0.93  --prep_def_merge_tr_red                 false
% 3.39/0.93  --prep_def_merge_tr_cl                  false
% 3.39/0.93  --smt_preprocessing                     true
% 3.39/0.93  --smt_ac_axioms                         fast
% 3.39/0.93  --preprocessed_out                      false
% 3.39/0.93  --preprocessed_stats                    false
% 3.39/0.93  
% 3.39/0.93  ------ Abstraction refinement Options
% 3.39/0.93  
% 3.39/0.93  --abstr_ref                             []
% 3.39/0.93  --abstr_ref_prep                        false
% 3.39/0.93  --abstr_ref_until_sat                   false
% 3.39/0.93  --abstr_ref_sig_restrict                funpre
% 3.39/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.93  --abstr_ref_under                       []
% 3.39/0.93  
% 3.39/0.93  ------ SAT Options
% 3.39/0.93  
% 3.39/0.93  --sat_mode                              false
% 3.39/0.93  --sat_fm_restart_options                ""
% 3.39/0.93  --sat_gr_def                            false
% 3.39/0.93  --sat_epr_types                         true
% 3.39/0.93  --sat_non_cyclic_types                  false
% 3.39/0.93  --sat_finite_models                     false
% 3.39/0.93  --sat_fm_lemmas                         false
% 3.39/0.93  --sat_fm_prep                           false
% 3.39/0.93  --sat_fm_uc_incr                        true
% 3.39/0.93  --sat_out_model                         small
% 3.39/0.93  --sat_out_clauses                       false
% 3.39/0.93  
% 3.39/0.93  ------ QBF Options
% 3.39/0.93  
% 3.39/0.93  --qbf_mode                              false
% 3.39/0.93  --qbf_elim_univ                         false
% 3.39/0.93  --qbf_dom_inst                          none
% 3.39/0.93  --qbf_dom_pre_inst                      false
% 3.39/0.93  --qbf_sk_in                             false
% 3.39/0.93  --qbf_pred_elim                         true
% 3.39/0.93  --qbf_split                             512
% 3.39/0.93  
% 3.39/0.93  ------ BMC1 Options
% 3.39/0.93  
% 3.39/0.93  --bmc1_incremental                      false
% 3.39/0.93  --bmc1_axioms                           reachable_all
% 3.39/0.93  --bmc1_min_bound                        0
% 3.39/0.93  --bmc1_max_bound                        -1
% 3.39/0.93  --bmc1_max_bound_default                -1
% 3.39/0.93  --bmc1_symbol_reachability              true
% 3.39/0.93  --bmc1_property_lemmas                  false
% 3.39/0.93  --bmc1_k_induction                      false
% 3.39/0.93  --bmc1_non_equiv_states                 false
% 3.39/0.93  --bmc1_deadlock                         false
% 3.39/0.93  --bmc1_ucm                              false
% 3.39/0.93  --bmc1_add_unsat_core                   none
% 3.39/0.93  --bmc1_unsat_core_children              false
% 3.39/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.93  --bmc1_out_stat                         full
% 3.39/0.93  --bmc1_ground_init                      false
% 3.39/0.93  --bmc1_pre_inst_next_state              false
% 3.39/0.93  --bmc1_pre_inst_state                   false
% 3.39/0.93  --bmc1_pre_inst_reach_state             false
% 3.39/0.93  --bmc1_out_unsat_core                   false
% 3.39/0.93  --bmc1_aig_witness_out                  false
% 3.39/0.93  --bmc1_verbose                          false
% 3.39/0.93  --bmc1_dump_clauses_tptp                false
% 3.39/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.93  --bmc1_dump_file                        -
% 3.39/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.93  --bmc1_ucm_extend_mode                  1
% 3.39/0.93  --bmc1_ucm_init_mode                    2
% 3.39/0.93  --bmc1_ucm_cone_mode                    none
% 3.39/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.93  --bmc1_ucm_relax_model                  4
% 3.39/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.93  --bmc1_ucm_layered_model                none
% 3.39/0.93  --bmc1_ucm_max_lemma_size               10
% 3.39/0.93  
% 3.39/0.93  ------ AIG Options
% 3.39/0.93  
% 3.39/0.93  --aig_mode                              false
% 3.39/0.93  
% 3.39/0.93  ------ Instantiation Options
% 3.39/0.93  
% 3.39/0.93  --instantiation_flag                    true
% 3.39/0.93  --inst_sos_flag                         false
% 3.39/0.93  --inst_sos_phase                        true
% 3.39/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel_side                     num_symb
% 3.39/0.93  --inst_solver_per_active                1400
% 3.39/0.93  --inst_solver_calls_frac                1.
% 3.39/0.93  --inst_passive_queue_type               priority_queues
% 3.39/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.93  --inst_passive_queues_freq              [25;2]
% 3.39/0.93  --inst_dismatching                      true
% 3.39/0.93  --inst_eager_unprocessed_to_passive     true
% 3.39/0.93  --inst_prop_sim_given                   true
% 3.39/0.93  --inst_prop_sim_new                     false
% 3.39/0.93  --inst_subs_new                         false
% 3.39/0.93  --inst_eq_res_simp                      false
% 3.39/0.93  --inst_subs_given                       false
% 3.39/0.93  --inst_orphan_elimination               true
% 3.39/0.93  --inst_learning_loop_flag               true
% 3.39/0.93  --inst_learning_start                   3000
% 3.39/0.93  --inst_learning_factor                  2
% 3.39/0.93  --inst_start_prop_sim_after_learn       3
% 3.39/0.93  --inst_sel_renew                        solver
% 3.39/0.93  --inst_lit_activity_flag                true
% 3.39/0.93  --inst_restr_to_given                   false
% 3.39/0.93  --inst_activity_threshold               500
% 3.39/0.93  --inst_out_proof                        true
% 3.39/0.93  
% 3.39/0.93  ------ Resolution Options
% 3.39/0.93  
% 3.39/0.93  --resolution_flag                       true
% 3.39/0.93  --res_lit_sel                           adaptive
% 3.39/0.93  --res_lit_sel_side                      none
% 3.39/0.93  --res_ordering                          kbo
% 3.39/0.93  --res_to_prop_solver                    active
% 3.39/0.93  --res_prop_simpl_new                    false
% 3.39/0.93  --res_prop_simpl_given                  true
% 3.39/0.93  --res_passive_queue_type                priority_queues
% 3.39/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.93  --res_passive_queues_freq               [15;5]
% 3.39/0.93  --res_forward_subs                      full
% 3.39/0.93  --res_backward_subs                     full
% 3.39/0.93  --res_forward_subs_resolution           true
% 3.39/0.93  --res_backward_subs_resolution          true
% 3.39/0.93  --res_orphan_elimination                true
% 3.39/0.93  --res_time_limit                        2.
% 3.39/0.93  --res_out_proof                         true
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Options
% 3.39/0.93  
% 3.39/0.93  --superposition_flag                    true
% 3.39/0.93  --sup_passive_queue_type                priority_queues
% 3.39/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.93  --demod_completeness_check              fast
% 3.39/0.93  --demod_use_ground                      true
% 3.39/0.93  --sup_to_prop_solver                    passive
% 3.39/0.93  --sup_prop_simpl_new                    true
% 3.39/0.93  --sup_prop_simpl_given                  true
% 3.39/0.93  --sup_fun_splitting                     false
% 3.39/0.93  --sup_smt_interval                      50000
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Simplification Setup
% 3.39/0.93  
% 3.39/0.93  --sup_indices_passive                   []
% 3.39/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_full_bw                           [BwDemod]
% 3.39/0.93  --sup_immed_triv                        [TrivRules]
% 3.39/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_immed_bw_main                     []
% 3.39/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  
% 3.39/0.93  ------ Combination Options
% 3.39/0.93  
% 3.39/0.93  --comb_res_mult                         3
% 3.39/0.93  --comb_sup_mult                         2
% 3.39/0.93  --comb_inst_mult                        10
% 3.39/0.93  
% 3.39/0.93  ------ Debug Options
% 3.39/0.93  
% 3.39/0.93  --dbg_backtrace                         false
% 3.39/0.93  --dbg_dump_prop_clauses                 false
% 3.39/0.93  --dbg_dump_prop_clauses_file            -
% 3.39/0.93  --dbg_out_stat                          false
% 3.39/0.93  ------ Parsing...
% 3.39/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/0.93  ------ Proving...
% 3.39/0.93  ------ Problem Properties 
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  clauses                                 18
% 3.39/0.93  conjectures                             3
% 3.39/0.93  EPR                                     1
% 3.39/0.93  Horn                                    11
% 3.39/0.93  unary                                   5
% 3.39/0.93  binary                                  5
% 3.39/0.93  lits                                    39
% 3.39/0.93  lits eq                                 9
% 3.39/0.93  fd_pure                                 0
% 3.39/0.93  fd_pseudo                               0
% 3.39/0.93  fd_cond                                 0
% 3.39/0.93  fd_pseudo_cond                          2
% 3.39/0.93  AC symbols                              0
% 3.39/0.93  
% 3.39/0.93  ------ Schedule dynamic 5 is on 
% 3.39/0.93  
% 3.39/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  ------ 
% 3.39/0.93  Current options:
% 3.39/0.93  ------ 
% 3.39/0.93  
% 3.39/0.93  ------ Input Options
% 3.39/0.93  
% 3.39/0.93  --out_options                           all
% 3.39/0.93  --tptp_safe_out                         true
% 3.39/0.93  --problem_path                          ""
% 3.39/0.93  --include_path                          ""
% 3.39/0.93  --clausifier                            res/vclausify_rel
% 3.39/0.93  --clausifier_options                    --mode clausify
% 3.39/0.93  --stdin                                 false
% 3.39/0.93  --stats_out                             all
% 3.39/0.93  
% 3.39/0.93  ------ General Options
% 3.39/0.93  
% 3.39/0.93  --fof                                   false
% 3.39/0.93  --time_out_real                         305.
% 3.39/0.93  --time_out_virtual                      -1.
% 3.39/0.93  --symbol_type_check                     false
% 3.39/0.93  --clausify_out                          false
% 3.39/0.93  --sig_cnt_out                           false
% 3.39/0.93  --trig_cnt_out                          false
% 3.39/0.93  --trig_cnt_out_tolerance                1.
% 3.39/0.93  --trig_cnt_out_sk_spl                   false
% 3.39/0.93  --abstr_cl_out                          false
% 3.39/0.93  
% 3.39/0.93  ------ Global Options
% 3.39/0.93  
% 3.39/0.93  --schedule                              default
% 3.39/0.93  --add_important_lit                     false
% 3.39/0.93  --prop_solver_per_cl                    1000
% 3.39/0.93  --min_unsat_core                        false
% 3.39/0.93  --soft_assumptions                      false
% 3.39/0.93  --soft_lemma_size                       3
% 3.39/0.93  --prop_impl_unit_size                   0
% 3.39/0.93  --prop_impl_unit                        []
% 3.39/0.93  --share_sel_clauses                     true
% 3.39/0.93  --reset_solvers                         false
% 3.39/0.93  --bc_imp_inh                            [conj_cone]
% 3.39/0.93  --conj_cone_tolerance                   3.
% 3.39/0.93  --extra_neg_conj                        none
% 3.39/0.93  --large_theory_mode                     true
% 3.39/0.93  --prolific_symb_bound                   200
% 3.39/0.93  --lt_threshold                          2000
% 3.39/0.93  --clause_weak_htbl                      true
% 3.39/0.93  --gc_record_bc_elim                     false
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing Options
% 3.39/0.93  
% 3.39/0.93  --preprocessing_flag                    true
% 3.39/0.93  --time_out_prep_mult                    0.1
% 3.39/0.93  --splitting_mode                        input
% 3.39/0.93  --splitting_grd                         true
% 3.39/0.93  --splitting_cvd                         false
% 3.39/0.93  --splitting_cvd_svl                     false
% 3.39/0.93  --splitting_nvd                         32
% 3.39/0.93  --sub_typing                            true
% 3.39/0.93  --prep_gs_sim                           true
% 3.39/0.93  --prep_unflatten                        true
% 3.39/0.93  --prep_res_sim                          true
% 3.39/0.93  --prep_upred                            true
% 3.39/0.93  --prep_sem_filter                       exhaustive
% 3.39/0.93  --prep_sem_filter_out                   false
% 3.39/0.93  --pred_elim                             true
% 3.39/0.93  --res_sim_input                         true
% 3.39/0.93  --eq_ax_congr_red                       true
% 3.39/0.93  --pure_diseq_elim                       true
% 3.39/0.93  --brand_transform                       false
% 3.39/0.93  --non_eq_to_eq                          false
% 3.39/0.93  --prep_def_merge                        true
% 3.39/0.93  --prep_def_merge_prop_impl              false
% 3.39/0.93  --prep_def_merge_mbd                    true
% 3.39/0.93  --prep_def_merge_tr_red                 false
% 3.39/0.93  --prep_def_merge_tr_cl                  false
% 3.39/0.93  --smt_preprocessing                     true
% 3.39/0.93  --smt_ac_axioms                         fast
% 3.39/0.93  --preprocessed_out                      false
% 3.39/0.93  --preprocessed_stats                    false
% 3.39/0.93  
% 3.39/0.93  ------ Abstraction refinement Options
% 3.39/0.93  
% 3.39/0.93  --abstr_ref                             []
% 3.39/0.93  --abstr_ref_prep                        false
% 3.39/0.93  --abstr_ref_until_sat                   false
% 3.39/0.93  --abstr_ref_sig_restrict                funpre
% 3.39/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.93  --abstr_ref_under                       []
% 3.39/0.93  
% 3.39/0.93  ------ SAT Options
% 3.39/0.93  
% 3.39/0.93  --sat_mode                              false
% 3.39/0.93  --sat_fm_restart_options                ""
% 3.39/0.93  --sat_gr_def                            false
% 3.39/0.93  --sat_epr_types                         true
% 3.39/0.93  --sat_non_cyclic_types                  false
% 3.39/0.93  --sat_finite_models                     false
% 3.39/0.93  --sat_fm_lemmas                         false
% 3.39/0.93  --sat_fm_prep                           false
% 3.39/0.93  --sat_fm_uc_incr                        true
% 3.39/0.93  --sat_out_model                         small
% 3.39/0.93  --sat_out_clauses                       false
% 3.39/0.93  
% 3.39/0.93  ------ QBF Options
% 3.39/0.93  
% 3.39/0.93  --qbf_mode                              false
% 3.39/0.93  --qbf_elim_univ                         false
% 3.39/0.93  --qbf_dom_inst                          none
% 3.39/0.93  --qbf_dom_pre_inst                      false
% 3.39/0.93  --qbf_sk_in                             false
% 3.39/0.93  --qbf_pred_elim                         true
% 3.39/0.93  --qbf_split                             512
% 3.39/0.93  
% 3.39/0.93  ------ BMC1 Options
% 3.39/0.93  
% 3.39/0.93  --bmc1_incremental                      false
% 3.39/0.93  --bmc1_axioms                           reachable_all
% 3.39/0.93  --bmc1_min_bound                        0
% 3.39/0.93  --bmc1_max_bound                        -1
% 3.39/0.93  --bmc1_max_bound_default                -1
% 3.39/0.93  --bmc1_symbol_reachability              true
% 3.39/0.93  --bmc1_property_lemmas                  false
% 3.39/0.93  --bmc1_k_induction                      false
% 3.39/0.93  --bmc1_non_equiv_states                 false
% 3.39/0.93  --bmc1_deadlock                         false
% 3.39/0.93  --bmc1_ucm                              false
% 3.39/0.93  --bmc1_add_unsat_core                   none
% 3.39/0.93  --bmc1_unsat_core_children              false
% 3.39/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.93  --bmc1_out_stat                         full
% 3.39/0.93  --bmc1_ground_init                      false
% 3.39/0.93  --bmc1_pre_inst_next_state              false
% 3.39/0.93  --bmc1_pre_inst_state                   false
% 3.39/0.93  --bmc1_pre_inst_reach_state             false
% 3.39/0.93  --bmc1_out_unsat_core                   false
% 3.39/0.93  --bmc1_aig_witness_out                  false
% 3.39/0.93  --bmc1_verbose                          false
% 3.39/0.93  --bmc1_dump_clauses_tptp                false
% 3.39/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.93  --bmc1_dump_file                        -
% 3.39/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.93  --bmc1_ucm_extend_mode                  1
% 3.39/0.93  --bmc1_ucm_init_mode                    2
% 3.39/0.93  --bmc1_ucm_cone_mode                    none
% 3.39/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.93  --bmc1_ucm_relax_model                  4
% 3.39/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.93  --bmc1_ucm_layered_model                none
% 3.39/0.93  --bmc1_ucm_max_lemma_size               10
% 3.39/0.93  
% 3.39/0.93  ------ AIG Options
% 3.39/0.93  
% 3.39/0.93  --aig_mode                              false
% 3.39/0.93  
% 3.39/0.93  ------ Instantiation Options
% 3.39/0.93  
% 3.39/0.93  --instantiation_flag                    true
% 3.39/0.93  --inst_sos_flag                         false
% 3.39/0.93  --inst_sos_phase                        true
% 3.39/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel_side                     none
% 3.39/0.93  --inst_solver_per_active                1400
% 3.39/0.93  --inst_solver_calls_frac                1.
% 3.39/0.93  --inst_passive_queue_type               priority_queues
% 3.39/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.93  --inst_passive_queues_freq              [25;2]
% 3.39/0.93  --inst_dismatching                      true
% 3.39/0.93  --inst_eager_unprocessed_to_passive     true
% 3.39/0.93  --inst_prop_sim_given                   true
% 3.39/0.93  --inst_prop_sim_new                     false
% 3.39/0.93  --inst_subs_new                         false
% 3.39/0.93  --inst_eq_res_simp                      false
% 3.39/0.93  --inst_subs_given                       false
% 3.39/0.93  --inst_orphan_elimination               true
% 3.39/0.93  --inst_learning_loop_flag               true
% 3.39/0.93  --inst_learning_start                   3000
% 3.39/0.93  --inst_learning_factor                  2
% 3.39/0.93  --inst_start_prop_sim_after_learn       3
% 3.39/0.93  --inst_sel_renew                        solver
% 3.39/0.93  --inst_lit_activity_flag                true
% 3.39/0.93  --inst_restr_to_given                   false
% 3.39/0.93  --inst_activity_threshold               500
% 3.39/0.93  --inst_out_proof                        true
% 3.39/0.93  
% 3.39/0.93  ------ Resolution Options
% 3.39/0.93  
% 3.39/0.93  --resolution_flag                       false
% 3.39/0.93  --res_lit_sel                           adaptive
% 3.39/0.93  --res_lit_sel_side                      none
% 3.39/0.93  --res_ordering                          kbo
% 3.39/0.93  --res_to_prop_solver                    active
% 3.39/0.93  --res_prop_simpl_new                    false
% 3.39/0.93  --res_prop_simpl_given                  true
% 3.39/0.93  --res_passive_queue_type                priority_queues
% 3.39/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.93  --res_passive_queues_freq               [15;5]
% 3.39/0.93  --res_forward_subs                      full
% 3.39/0.93  --res_backward_subs                     full
% 3.39/0.93  --res_forward_subs_resolution           true
% 3.39/0.93  --res_backward_subs_resolution          true
% 3.39/0.93  --res_orphan_elimination                true
% 3.39/0.93  --res_time_limit                        2.
% 3.39/0.93  --res_out_proof                         true
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Options
% 3.39/0.93  
% 3.39/0.93  --superposition_flag                    true
% 3.39/0.93  --sup_passive_queue_type                priority_queues
% 3.39/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.93  --demod_completeness_check              fast
% 3.39/0.93  --demod_use_ground                      true
% 3.39/0.93  --sup_to_prop_solver                    passive
% 3.39/0.93  --sup_prop_simpl_new                    true
% 3.39/0.93  --sup_prop_simpl_given                  true
% 3.39/0.93  --sup_fun_splitting                     false
% 3.39/0.93  --sup_smt_interval                      50000
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Simplification Setup
% 3.39/0.93  
% 3.39/0.93  --sup_indices_passive                   []
% 3.39/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_full_bw                           [BwDemod]
% 3.39/0.93  --sup_immed_triv                        [TrivRules]
% 3.39/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_immed_bw_main                     []
% 3.39/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  
% 3.39/0.93  ------ Combination Options
% 3.39/0.93  
% 3.39/0.93  --comb_res_mult                         3
% 3.39/0.93  --comb_sup_mult                         2
% 3.39/0.93  --comb_inst_mult                        10
% 3.39/0.93  
% 3.39/0.93  ------ Debug Options
% 3.39/0.93  
% 3.39/0.93  --dbg_backtrace                         false
% 3.39/0.93  --dbg_dump_prop_clauses                 false
% 3.39/0.93  --dbg_dump_prop_clauses_file            -
% 3.39/0.93  --dbg_out_stat                          false
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  ------ Proving...
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  % SZS status Theorem for theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  fof(f2,axiom,(
% 3.39/0.93    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f20,plain,(
% 3.39/0.93    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.39/0.93    inference(ennf_transformation,[],[f2])).
% 3.39/0.93  
% 3.39/0.93  fof(f24,plain,(
% 3.39/0.93    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.39/0.93    inference(nnf_transformation,[],[f20])).
% 3.39/0.93  
% 3.39/0.93  fof(f38,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f24])).
% 3.39/0.93  
% 3.39/0.93  fof(f17,conjecture,(
% 3.39/0.93    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f18,negated_conjecture,(
% 3.39/0.93    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.39/0.93    inference(negated_conjecture,[],[f17])).
% 3.39/0.93  
% 3.39/0.93  fof(f23,plain,(
% 3.39/0.93    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.39/0.93    inference(ennf_transformation,[],[f18])).
% 3.39/0.93  
% 3.39/0.93  fof(f31,plain,(
% 3.39/0.93    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.39/0.93    inference(nnf_transformation,[],[f23])).
% 3.39/0.93  
% 3.39/0.93  fof(f32,plain,(
% 3.39/0.93    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.39/0.93    inference(flattening,[],[f31])).
% 3.39/0.93  
% 3.39/0.93  fof(f33,plain,(
% 3.39/0.93    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))) & ((sK2 != sK4 & r2_hidden(sK2,sK3)) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))))),
% 3.39/0.93    introduced(choice_axiom,[])).
% 3.39/0.93  
% 3.39/0.93  fof(f34,plain,(
% 3.39/0.93    (sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))) & ((sK2 != sK4 & r2_hidden(sK2,sK3)) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))))),
% 3.39/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f33])).
% 3.39/0.93  
% 3.39/0.93  fof(f61,plain,(
% 3.39/0.93    sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 3.39/0.93    inference(cnf_transformation,[],[f34])).
% 3.39/0.93  
% 3.39/0.93  fof(f5,axiom,(
% 3.39/0.93    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f44,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f5])).
% 3.39/0.93  
% 3.39/0.93  fof(f10,axiom,(
% 3.39/0.93    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f52,plain,(
% 3.39/0.93    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f10])).
% 3.39/0.93  
% 3.39/0.93  fof(f11,axiom,(
% 3.39/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f53,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f11])).
% 3.39/0.93  
% 3.39/0.93  fof(f12,axiom,(
% 3.39/0.93    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f54,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f12])).
% 3.39/0.93  
% 3.39/0.93  fof(f13,axiom,(
% 3.39/0.93    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f55,plain,(
% 3.39/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f13])).
% 3.39/0.93  
% 3.39/0.93  fof(f14,axiom,(
% 3.39/0.93    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f56,plain,(
% 3.39/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f14])).
% 3.39/0.93  
% 3.39/0.93  fof(f15,axiom,(
% 3.39/0.93    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f57,plain,(
% 3.39/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f15])).
% 3.39/0.93  
% 3.39/0.93  fof(f16,axiom,(
% 3.39/0.93    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f58,plain,(
% 3.39/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f16])).
% 3.39/0.93  
% 3.39/0.93  fof(f62,plain,(
% 3.39/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f57,f58])).
% 3.39/0.93  
% 3.39/0.93  fof(f63,plain,(
% 3.39/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f56,f62])).
% 3.39/0.93  
% 3.39/0.93  fof(f64,plain,(
% 3.39/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f55,f63])).
% 3.39/0.93  
% 3.39/0.93  fof(f65,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f54,f64])).
% 3.39/0.93  
% 3.39/0.93  fof(f66,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f53,f65])).
% 3.39/0.93  
% 3.39/0.93  fof(f67,plain,(
% 3.39/0.93    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f52,f66])).
% 3.39/0.93  
% 3.39/0.93  fof(f73,plain,(
% 3.39/0.93    sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.39/0.93    inference(definition_unfolding,[],[f61,f44,f67])).
% 3.39/0.93  
% 3.39/0.93  fof(f59,plain,(
% 3.39/0.93    r2_hidden(sK2,sK3) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 3.39/0.93    inference(cnf_transformation,[],[f34])).
% 3.39/0.93  
% 3.39/0.93  fof(f75,plain,(
% 3.39/0.93    r2_hidden(sK2,sK3) | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.39/0.93    inference(definition_unfolding,[],[f59,f44,f67])).
% 3.39/0.93  
% 3.39/0.93  fof(f36,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.39/0.93    inference(cnf_transformation,[],[f24])).
% 3.39/0.93  
% 3.39/0.93  fof(f1,axiom,(
% 3.39/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f35,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f1])).
% 3.39/0.93  
% 3.39/0.93  fof(f6,axiom,(
% 3.39/0.93    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f45,plain,(
% 3.39/0.93    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f6])).
% 3.39/0.93  
% 3.39/0.93  fof(f7,axiom,(
% 3.39/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f22,plain,(
% 3.39/0.93    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.39/0.93    inference(ennf_transformation,[],[f7])).
% 3.39/0.93  
% 3.39/0.93  fof(f46,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f22])).
% 3.39/0.93  
% 3.39/0.93  fof(f4,axiom,(
% 3.39/0.93    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f43,plain,(
% 3.39/0.93    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.39/0.93    inference(cnf_transformation,[],[f4])).
% 3.39/0.93  
% 3.39/0.93  fof(f3,axiom,(
% 3.39/0.93    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f19,plain,(
% 3.39/0.93    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.39/0.93    inference(rectify,[],[f3])).
% 3.39/0.93  
% 3.39/0.93  fof(f21,plain,(
% 3.39/0.93    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.39/0.93    inference(ennf_transformation,[],[f19])).
% 3.39/0.93  
% 3.39/0.93  fof(f25,plain,(
% 3.39/0.93    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.39/0.93    introduced(choice_axiom,[])).
% 3.39/0.93  
% 3.39/0.93  fof(f26,plain,(
% 3.39/0.93    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.39/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f25])).
% 3.39/0.93  
% 3.39/0.93  fof(f42,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f26])).
% 3.39/0.93  
% 3.39/0.93  fof(f9,axiom,(
% 3.39/0.93    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f27,plain,(
% 3.39/0.93    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.39/0.93    inference(nnf_transformation,[],[f9])).
% 3.39/0.93  
% 3.39/0.93  fof(f28,plain,(
% 3.39/0.93    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.39/0.93    inference(rectify,[],[f27])).
% 3.39/0.93  
% 3.39/0.93  fof(f29,plain,(
% 3.39/0.93    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.39/0.93    introduced(choice_axiom,[])).
% 3.39/0.93  
% 3.39/0.93  fof(f30,plain,(
% 3.39/0.93    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.39/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.39/0.93  
% 3.39/0.93  fof(f49,plain,(
% 3.39/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.39/0.93    inference(cnf_transformation,[],[f30])).
% 3.39/0.93  
% 3.39/0.93  fof(f71,plain,(
% 3.39/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.39/0.93    inference(definition_unfolding,[],[f49,f67])).
% 3.39/0.93  
% 3.39/0.93  fof(f76,plain,(
% 3.39/0.93    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 3.39/0.93    inference(equality_resolution,[],[f71])).
% 3.39/0.93  
% 3.39/0.93  fof(f77,plain,(
% 3.39/0.93    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 3.39/0.93    inference(equality_resolution,[],[f76])).
% 3.39/0.93  
% 3.39/0.93  fof(f48,plain,(
% 3.39/0.93    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.39/0.93    inference(cnf_transformation,[],[f30])).
% 3.39/0.93  
% 3.39/0.93  fof(f72,plain,(
% 3.39/0.93    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.39/0.93    inference(definition_unfolding,[],[f48,f67])).
% 3.39/0.93  
% 3.39/0.93  fof(f78,plain,(
% 3.39/0.93    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.39/0.93    inference(equality_resolution,[],[f72])).
% 3.39/0.93  
% 3.39/0.93  fof(f60,plain,(
% 3.39/0.93    sK2 != sK4 | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 3.39/0.93    inference(cnf_transformation,[],[f34])).
% 3.39/0.93  
% 3.39/0.93  fof(f74,plain,(
% 3.39/0.93    sK2 != sK4 | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.39/0.93    inference(definition_unfolding,[],[f60,f44,f67])).
% 3.39/0.93  
% 3.39/0.93  fof(f8,axiom,(
% 3.39/0.93    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f47,plain,(
% 3.39/0.93    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f8])).
% 3.39/0.93  
% 3.39/0.93  fof(f68,plain,(
% 3.39/0.93    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.39/0.93    inference(definition_unfolding,[],[f47,f44])).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2,plain,
% 3.39/0.93      ( ~ r2_hidden(X0,X1)
% 3.39/0.93      | r2_hidden(X0,X2)
% 3.39/0.93      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f38]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_721,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) != iProver_top
% 3.39/0.93      | r2_hidden(X0,X2) = iProver_top
% 3.39/0.93      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_16,negated_conjecture,
% 3.39/0.93      ( ~ r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 3.39/0.93      | ~ r2_hidden(sK2,sK3)
% 3.39/0.93      | sK2 = sK4 ),
% 3.39/0.93      inference(cnf_transformation,[],[f73]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_709,plain,
% 3.39/0.93      ( sK2 = sK4
% 3.39/0.93      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
% 3.39/0.93      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_6632,plain,
% 3.39/0.93      ( sK4 = sK2
% 3.39/0.93      | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 3.39/0.93      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_721,c_709]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_18,negated_conjecture,
% 3.39/0.93      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 3.39/0.93      | r2_hidden(sK2,sK3) ),
% 3.39/0.93      inference(cnf_transformation,[],[f75]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_707,plain,
% 3.39/0.93      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
% 3.39/0.93      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_4,plain,
% 3.39/0.93      ( r2_hidden(X0,X1)
% 3.39/0.93      | r2_hidden(X0,X2)
% 3.39/0.93      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f36]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_719,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) = iProver_top
% 3.39/0.93      | r2_hidden(X0,X2) = iProver_top
% 3.39/0.93      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_6592,plain,
% 3.39/0.93      ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 3.39/0.93      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_707,c_719]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_7194,plain,
% 3.39/0.93      ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 3.39/0.93      | sK4 = sK2 ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_6632,c_6592]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_7195,plain,
% 3.39/0.93      ( sK4 = sK2
% 3.39/0.93      | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
% 3.39/0.93      inference(renaming,[status(thm)],[c_7194]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_0,plain,
% 3.39/0.93      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f35]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_9,plain,
% 3.39/0.93      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f45]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_10,plain,
% 3.39/0.93      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.39/0.93      inference(cnf_transformation,[],[f46]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_203,plain,
% 3.39/0.93      ( X0 != X1 | k3_xboole_0(X1,X2) != X3 | k3_xboole_0(X3,X0) = X3 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_204,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_203]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_981,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_0,c_204]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_985,plain,
% 3.39/0.93      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_204,c_0]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1166,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_981,c_985]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1176,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 3.39/0.93      inference(light_normalisation,[status(thm)],[c_1166,c_981]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_3123,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_981,c_1176]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1145,plain,
% 3.39/0.93      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_981,c_0]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_983,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_204,c_204]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_989,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.39/0.93      inference(light_normalisation,[status(thm)],[c_983,c_204]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1535,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_0,c_989]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_3184,plain,
% 3.39/0.93      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 3.39/0.93      inference(light_normalisation,[status(thm)],[c_3123,c_1145,c_1535]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_3245,plain,
% 3.39/0.93      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_3184,c_0]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_8,plain,
% 3.39/0.93      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f43]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_715,plain,
% 3.39/0.93      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1051,plain,
% 3.39/0.93      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),X0)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_204,c_715]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_5,plain,
% 3.39/0.93      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f42]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_718,plain,
% 3.39/0.93      ( r1_xboole_0(X0,X1) != iProver_top
% 3.39/0.93      | r2_hidden(X2,X1) != iProver_top
% 3.39/0.93      | r2_hidden(X2,X0) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_4243,plain,
% 3.39/0.93      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),X1)) != iProver_top
% 3.39/0.93      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1051,c_718]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11260,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) = iProver_top
% 3.39/0.93      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_721,c_4243]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11417,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) = iProver_top
% 3.39/0.93      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_3245,c_11260]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11460,plain,
% 3.39/0.93      ( sK4 = sK2
% 3.39/0.93      | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_7195,c_11417]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_434,plain,( X0 = X0 ),theory(equality) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1033,plain,
% 3.39/0.93      ( sK2 = sK2 ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_434]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_14,plain,
% 3.39/0.93      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f77]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1618,plain,
% 3.39/0.93      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_14]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1619,plain,
% 3.39/0.93      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_1618]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_438,plain,
% 3.39/0.93      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.39/0.93      theory(equality) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_876,plain,
% 3.39/0.93      ( r2_hidden(X0,X1)
% 3.39/0.93      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 3.39/0.93      | X0 != X2
% 3.39/0.93      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_438]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1271,plain,
% 3.39/0.93      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.39/0.93      | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.39/0.93      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.39/0.93      | sK2 != X0 ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_876]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1902,plain,
% 3.39/0.93      ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.39/0.93      | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.39/0.93      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.39/0.93      | sK2 != sK2 ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_1271]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1903,plain,
% 3.39/0.93      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.39/0.93      | sK2 != sK2
% 3.39/0.93      | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 3.39/0.93      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_1902]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_440,plain,
% 3.39/0.93      ( X0 != X1
% 3.39/0.93      | X2 != X3
% 3.39/0.93      | X4 != X5
% 3.39/0.93      | X6 != X7
% 3.39/0.93      | X8 != X9
% 3.39/0.93      | X10 != X11
% 3.39/0.93      | X12 != X13
% 3.39/0.93      | X14 != X15
% 3.39/0.93      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.39/0.93      theory(equality) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_9010,plain,
% 3.39/0.93      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.39/0.93      | sK4 != sK2 ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_440]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11755,plain,
% 3.39/0.93      ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_11460,c_1033,c_1619,c_1903,c_9010]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_15,plain,
% 3.39/0.93      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.39/0.93      inference(cnf_transformation,[],[f78]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_710,plain,
% 3.39/0.93      ( X0 = X1
% 3.39/0.93      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11762,plain,
% 3.39/0.93      ( sK4 = sK2 ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_11755,c_710]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_17,negated_conjecture,
% 3.39/0.93      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 3.39/0.93      | sK2 != sK4 ),
% 3.39/0.93      inference(cnf_transformation,[],[f74]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_708,plain,
% 3.39/0.93      ( sK2 != sK4
% 3.39/0.93      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_12020,plain,
% 3.39/0.93      ( sK2 != sK2
% 3.39/0.93      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 3.39/0.93      inference(demodulation,[status(thm)],[c_11762,c_708]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_12021,plain,
% 3.39/0.93      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 3.39/0.93      inference(equality_resolution_simp,[status(thm)],[c_12020]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11,plain,
% 3.39/0.93      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f68]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_714,plain,
% 3.39/0.93      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_4239,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) != iProver_top
% 3.39/0.93      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_714,c_718]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_13254,plain,
% 3.39/0.93      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_12021,c_4239]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(contradiction,plain,
% 3.39/0.93      ( $false ),
% 3.39/0.93      inference(minisat,[status(thm)],[c_13254,c_1619]) ).
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  ------                               Statistics
% 3.39/0.93  
% 3.39/0.93  ------ General
% 3.39/0.93  
% 3.39/0.93  abstr_ref_over_cycles:                  0
% 3.39/0.93  abstr_ref_under_cycles:                 0
% 3.39/0.93  gc_basic_clause_elim:                   0
% 3.39/0.93  forced_gc_time:                         0
% 3.39/0.93  parsing_time:                           0.012
% 3.39/0.93  unif_index_cands_time:                  0.
% 3.39/0.93  unif_index_add_time:                    0.
% 3.39/0.93  orderings_time:                         0.
% 3.39/0.93  out_proof_time:                         0.013
% 3.39/0.93  total_time:                             0.471
% 3.39/0.93  num_of_symbols:                         42
% 3.39/0.93  num_of_terms:                           11548
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing
% 3.39/0.93  
% 3.39/0.93  num_of_splits:                          0
% 3.39/0.93  num_of_split_atoms:                     0
% 3.39/0.93  num_of_reused_defs:                     0
% 3.39/0.93  num_eq_ax_congr_red:                    13
% 3.39/0.93  num_of_sem_filtered_clauses:            1
% 3.39/0.93  num_of_subtypes:                        0
% 3.39/0.93  monotx_restored_types:                  0
% 3.39/0.93  sat_num_of_epr_types:                   0
% 3.39/0.93  sat_num_of_non_cyclic_types:            0
% 3.39/0.93  sat_guarded_non_collapsed_types:        0
% 3.39/0.93  num_pure_diseq_elim:                    0
% 3.39/0.93  simp_replaced_by:                       0
% 3.39/0.93  res_preprocessed:                       88
% 3.39/0.93  prep_upred:                             0
% 3.39/0.93  prep_unflattend:                        10
% 3.39/0.93  smt_new_axioms:                         0
% 3.39/0.93  pred_elim_cands:                        2
% 3.39/0.93  pred_elim:                              1
% 3.39/0.93  pred_elim_cl:                           1
% 3.39/0.93  pred_elim_cycles:                       3
% 3.39/0.93  merged_defs:                            0
% 3.39/0.93  merged_defs_ncl:                        0
% 3.39/0.93  bin_hyper_res:                          0
% 3.39/0.93  prep_cycles:                            4
% 3.39/0.93  pred_elim_time:                         0.001
% 3.39/0.93  splitting_time:                         0.
% 3.39/0.93  sem_filter_time:                        0.
% 3.39/0.93  monotx_time:                            0.
% 3.39/0.93  subtype_inf_time:                       0.
% 3.39/0.93  
% 3.39/0.93  ------ Problem properties
% 3.39/0.93  
% 3.39/0.93  clauses:                                18
% 3.39/0.93  conjectures:                            3
% 3.39/0.93  epr:                                    1
% 3.39/0.93  horn:                                   11
% 3.39/0.93  ground:                                 3
% 3.39/0.93  unary:                                  5
% 3.39/0.93  binary:                                 5
% 3.39/0.93  lits:                                   39
% 3.39/0.93  lits_eq:                                9
% 3.39/0.93  fd_pure:                                0
% 3.39/0.93  fd_pseudo:                              0
% 3.39/0.93  fd_cond:                                0
% 3.39/0.93  fd_pseudo_cond:                         2
% 3.39/0.93  ac_symbols:                             0
% 3.39/0.93  
% 3.39/0.93  ------ Propositional Solver
% 3.39/0.93  
% 3.39/0.93  prop_solver_calls:                      27
% 3.39/0.93  prop_fast_solver_calls:                 638
% 3.39/0.93  smt_solver_calls:                       0
% 3.39/0.93  smt_fast_solver_calls:                  0
% 3.39/0.93  prop_num_of_clauses:                    3330
% 3.39/0.93  prop_preprocess_simplified:             6945
% 3.39/0.93  prop_fo_subsumed:                       30
% 3.39/0.93  prop_solver_time:                       0.
% 3.39/0.93  smt_solver_time:                        0.
% 3.39/0.93  smt_fast_solver_time:                   0.
% 3.39/0.93  prop_fast_solver_time:                  0.
% 3.39/0.93  prop_unsat_core_time:                   0.
% 3.39/0.93  
% 3.39/0.93  ------ QBF
% 3.39/0.93  
% 3.39/0.93  qbf_q_res:                              0
% 3.39/0.93  qbf_num_tautologies:                    0
% 3.39/0.93  qbf_prep_cycles:                        0
% 3.39/0.93  
% 3.39/0.93  ------ BMC1
% 3.39/0.93  
% 3.39/0.93  bmc1_current_bound:                     -1
% 3.39/0.93  bmc1_last_solved_bound:                 -1
% 3.39/0.93  bmc1_unsat_core_size:                   -1
% 3.39/0.93  bmc1_unsat_core_parents_size:           -1
% 3.39/0.93  bmc1_merge_next_fun:                    0
% 3.39/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.39/0.93  
% 3.39/0.93  ------ Instantiation
% 3.39/0.93  
% 3.39/0.93  inst_num_of_clauses:                    785
% 3.39/0.93  inst_num_in_passive:                    129
% 3.39/0.93  inst_num_in_active:                     324
% 3.39/0.93  inst_num_in_unprocessed:                332
% 3.39/0.93  inst_num_of_loops:                      420
% 3.39/0.93  inst_num_of_learning_restarts:          0
% 3.39/0.93  inst_num_moves_active_passive:          94
% 3.39/0.93  inst_lit_activity:                      0
% 3.39/0.93  inst_lit_activity_moves:                0
% 3.39/0.93  inst_num_tautologies:                   0
% 3.39/0.93  inst_num_prop_implied:                  0
% 3.39/0.93  inst_num_existing_simplified:           0
% 3.39/0.93  inst_num_eq_res_simplified:             0
% 3.39/0.93  inst_num_child_elim:                    0
% 3.39/0.93  inst_num_of_dismatching_blockings:      2576
% 3.39/0.93  inst_num_of_non_proper_insts:           1590
% 3.39/0.93  inst_num_of_duplicates:                 0
% 3.39/0.93  inst_inst_num_from_inst_to_res:         0
% 3.39/0.93  inst_dismatching_checking_time:         0.
% 3.39/0.93  
% 3.39/0.93  ------ Resolution
% 3.39/0.93  
% 3.39/0.93  res_num_of_clauses:                     0
% 3.39/0.93  res_num_in_passive:                     0
% 3.39/0.93  res_num_in_active:                      0
% 3.39/0.93  res_num_of_loops:                       92
% 3.39/0.93  res_forward_subset_subsumed:            39
% 3.39/0.93  res_backward_subset_subsumed:           12
% 3.39/0.93  res_forward_subsumed:                   0
% 3.39/0.93  res_backward_subsumed:                  0
% 3.39/0.93  res_forward_subsumption_resolution:     0
% 3.39/0.93  res_backward_subsumption_resolution:    0
% 3.39/0.93  res_clause_to_clause_subsumption:       2328
% 3.39/0.93  res_orphan_elimination:                 0
% 3.39/0.93  res_tautology_del:                      83
% 3.39/0.93  res_num_eq_res_simplified:              0
% 3.39/0.93  res_num_sel_changes:                    0
% 3.39/0.93  res_moves_from_active_to_pass:          0
% 3.39/0.93  
% 3.39/0.93  ------ Superposition
% 3.39/0.93  
% 3.39/0.93  sup_time_total:                         0.
% 3.39/0.93  sup_time_generating:                    0.
% 3.39/0.93  sup_time_sim_full:                      0.
% 3.39/0.93  sup_time_sim_immed:                     0.
% 3.39/0.93  
% 3.39/0.93  sup_num_of_clauses:                     199
% 3.39/0.93  sup_num_in_active:                      69
% 3.39/0.93  sup_num_in_passive:                     130
% 3.39/0.93  sup_num_of_loops:                       82
% 3.39/0.93  sup_fw_superposition:                   1088
% 3.39/0.93  sup_bw_superposition:                   360
% 3.39/0.93  sup_immediate_simplified:               426
% 3.39/0.93  sup_given_eliminated:                   1
% 3.39/0.93  comparisons_done:                       0
% 3.39/0.93  comparisons_avoided:                    10
% 3.39/0.93  
% 3.39/0.93  ------ Simplifications
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  sim_fw_subset_subsumed:                 14
% 3.39/0.93  sim_bw_subset_subsumed:                 2
% 3.39/0.93  sim_fw_subsumed:                        29
% 3.39/0.93  sim_bw_subsumed:                        0
% 3.39/0.93  sim_fw_subsumption_res:                 1
% 3.39/0.93  sim_bw_subsumption_res:                 0
% 3.39/0.93  sim_tautology_del:                      27
% 3.39/0.93  sim_eq_tautology_del:                   22
% 3.39/0.93  sim_eq_res_simp:                        1
% 3.39/0.93  sim_fw_demodulated:                     127
% 3.39/0.93  sim_bw_demodulated:                     13
% 3.39/0.93  sim_light_normalised:                   263
% 3.39/0.93  sim_joinable_taut:                      0
% 3.39/0.93  sim_joinable_simp:                      0
% 3.39/0.93  sim_ac_normalised:                      0
% 3.39/0.93  sim_smt_subsumption:                    0
% 3.39/0.93  
%------------------------------------------------------------------------------
