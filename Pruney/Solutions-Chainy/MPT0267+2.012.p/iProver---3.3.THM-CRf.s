%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:31 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 314 expanded)
%              Number of clauses        :   54 (  66 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   21
%              Number of atoms          :  310 ( 803 expanded)
%              Number of equality atoms :  167 ( 352 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
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

fof(f33,plain,
    ( ( sK2 = sK4
      | ~ r2_hidden(sK2,sK3)
      | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) )
    & ( ( sK2 != sK4
        & r2_hidden(sK2,sK3) )
      | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f32])).

fof(f59,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f71,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f59,f43,f65])).

fof(f57,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f57,f43,f65])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f76,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f58,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f58,f43,f65])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f74,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f75,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f74])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19982,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ r2_hidden(sK2,sK3)
    | sK2 = sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_19975,plain,
    ( sK2 = sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_20123,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19982,c_19975])).

cnf(c_4112,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4108,plain,
    ( sK2 = sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4222,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_4108])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4106,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4111,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4214,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4106,c_4111])).

cnf(c_4272,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | sK4 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4222,c_4214])).

cnf(c_4273,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4272])).

cnf(c_20191,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | sK4 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20123,c_4273])).

cnf(c_20192,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_20191])).

cnf(c_8,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19979,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19980,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20099,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19979,c_19980])).

cnf(c_20147,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19982,c_20099])).

cnf(c_4109,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4110,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4182,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_4110])).

cnf(c_4220,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_4182])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4420,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4609,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4414,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4416,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4559,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4414,c_4416])).

cnf(c_4915,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4609,c_4559])).

cnf(c_7837,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4420,c_4915])).

cnf(c_20229,plain,
    ( r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20147,c_4220,c_7837])).

cnf(c_20230,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20229])).

cnf(c_20236,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20192,c_20230])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_19976,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20252,plain,
    ( sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_20236,c_19976])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19974,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20279,plain,
    ( sK2 != sK2
    | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20252,c_19974])).

cnf(c_20280,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_20279])).

cnf(c_19978,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20062,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19978,c_19980])).

cnf(c_20293,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20280,c_20062])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19977,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20307,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20293,c_19977])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.32/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.50  
% 7.32/1.50  ------  iProver source info
% 7.32/1.50  
% 7.32/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.50  git: non_committed_changes: false
% 7.32/1.50  git: last_make_outside_of_git: false
% 7.32/1.50  
% 7.32/1.50  ------ 
% 7.32/1.50  ------ Parsing...
% 7.32/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  ------ Proving...
% 7.32/1.50  ------ Problem Properties 
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  clauses                                 18
% 7.32/1.50  conjectures                             5
% 7.32/1.50  EPR                                     1
% 7.32/1.50  Horn                                    11
% 7.32/1.50  unary                                   5
% 7.32/1.50  binary                                  5
% 7.32/1.50  lits                                    39
% 7.32/1.50  lits eq                                 9
% 7.32/1.50  fd_pure                                 0
% 7.32/1.50  fd_pseudo                               0
% 7.32/1.50  fd_cond                                 0
% 7.32/1.50  fd_pseudo_cond                          2
% 7.32/1.50  AC symbols                              0
% 7.32/1.50  
% 7.32/1.50  ------ Input Options Time Limit: Unbounded
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing...
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.32/1.50  Current options:
% 7.32/1.50  ------ 
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing...
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  % SZS status Theorem for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50   Resolution empty clause
% 7.32/1.50  
% 7.32/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  fof(f2,axiom,(
% 7.32/1.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f20,plain,(
% 7.32/1.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 7.32/1.50    inference(ennf_transformation,[],[f2])).
% 7.32/1.50  
% 7.32/1.50  fof(f23,plain,(
% 7.32/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 7.32/1.50    inference(nnf_transformation,[],[f20])).
% 7.32/1.50  
% 7.32/1.50  fof(f37,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f23])).
% 7.32/1.50  
% 7.32/1.50  fof(f16,conjecture,(
% 7.32/1.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f17,negated_conjecture,(
% 7.32/1.50    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.32/1.50    inference(negated_conjecture,[],[f16])).
% 7.32/1.50  
% 7.32/1.50  fof(f22,plain,(
% 7.32/1.50    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.32/1.50    inference(ennf_transformation,[],[f17])).
% 7.32/1.50  
% 7.32/1.50  fof(f30,plain,(
% 7.32/1.50    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.32/1.50    inference(nnf_transformation,[],[f22])).
% 7.32/1.50  
% 7.32/1.50  fof(f31,plain,(
% 7.32/1.50    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.32/1.50    inference(flattening,[],[f30])).
% 7.32/1.50  
% 7.32/1.50  fof(f32,plain,(
% 7.32/1.50    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))) & ((sK2 != sK4 & r2_hidden(sK2,sK3)) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f33,plain,(
% 7.32/1.50    (sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))) & ((sK2 != sK4 & r2_hidden(sK2,sK3)) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f59,plain,(
% 7.32/1.50    sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 7.32/1.50    inference(cnf_transformation,[],[f33])).
% 7.32/1.50  
% 7.32/1.50  fof(f5,axiom,(
% 7.32/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f43,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f5])).
% 7.32/1.50  
% 7.32/1.50  fof(f9,axiom,(
% 7.32/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f50,plain,(
% 7.32/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f9])).
% 7.32/1.50  
% 7.32/1.50  fof(f10,axiom,(
% 7.32/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f51,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f10])).
% 7.32/1.50  
% 7.32/1.50  fof(f11,axiom,(
% 7.32/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f52,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f11])).
% 7.32/1.50  
% 7.32/1.50  fof(f12,axiom,(
% 7.32/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f53,plain,(
% 7.32/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f12])).
% 7.32/1.50  
% 7.32/1.50  fof(f13,axiom,(
% 7.32/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f54,plain,(
% 7.32/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f13])).
% 7.32/1.50  
% 7.32/1.50  fof(f14,axiom,(
% 7.32/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f55,plain,(
% 7.32/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f14])).
% 7.32/1.50  
% 7.32/1.50  fof(f15,axiom,(
% 7.32/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f56,plain,(
% 7.32/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f15])).
% 7.32/1.50  
% 7.32/1.50  fof(f60,plain,(
% 7.32/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f55,f56])).
% 7.32/1.50  
% 7.32/1.50  fof(f61,plain,(
% 7.32/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f54,f60])).
% 7.32/1.50  
% 7.32/1.50  fof(f62,plain,(
% 7.32/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f53,f61])).
% 7.32/1.50  
% 7.32/1.50  fof(f63,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f52,f62])).
% 7.32/1.50  
% 7.32/1.50  fof(f64,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f51,f63])).
% 7.32/1.50  
% 7.32/1.50  fof(f65,plain,(
% 7.32/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f50,f64])).
% 7.32/1.50  
% 7.32/1.50  fof(f71,plain,(
% 7.32/1.50    sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 7.32/1.50    inference(definition_unfolding,[],[f59,f43,f65])).
% 7.32/1.50  
% 7.32/1.50  fof(f57,plain,(
% 7.32/1.50    r2_hidden(sK2,sK3) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 7.32/1.50    inference(cnf_transformation,[],[f33])).
% 7.32/1.50  
% 7.32/1.50  fof(f73,plain,(
% 7.32/1.50    r2_hidden(sK2,sK3) | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 7.32/1.50    inference(definition_unfolding,[],[f57,f43,f65])).
% 7.32/1.50  
% 7.32/1.50  fof(f35,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 7.32/1.50    inference(cnf_transformation,[],[f23])).
% 7.32/1.50  
% 7.32/1.50  fof(f4,axiom,(
% 7.32/1.50    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f42,plain,(
% 7.32/1.50    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.32/1.50    inference(cnf_transformation,[],[f4])).
% 7.32/1.50  
% 7.32/1.50  fof(f3,axiom,(
% 7.32/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f19,plain,(
% 7.32/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.50    inference(rectify,[],[f3])).
% 7.32/1.50  
% 7.32/1.50  fof(f21,plain,(
% 7.32/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.32/1.50    inference(ennf_transformation,[],[f19])).
% 7.32/1.50  
% 7.32/1.50  fof(f24,plain,(
% 7.32/1.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f25,plain,(
% 7.32/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).
% 7.32/1.50  
% 7.32/1.50  fof(f41,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f25])).
% 7.32/1.50  
% 7.32/1.50  fof(f38,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f23])).
% 7.32/1.50  
% 7.32/1.50  fof(f1,axiom,(
% 7.32/1.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f18,plain,(
% 7.32/1.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.32/1.50    inference(rectify,[],[f1])).
% 7.32/1.50  
% 7.32/1.50  fof(f34,plain,(
% 7.32/1.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.32/1.50    inference(cnf_transformation,[],[f18])).
% 7.32/1.50  
% 7.32/1.50  fof(f6,axiom,(
% 7.32/1.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f44,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f6])).
% 7.32/1.50  
% 7.32/1.50  fof(f7,axiom,(
% 7.32/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f45,plain,(
% 7.32/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f7])).
% 7.32/1.50  
% 7.32/1.50  fof(f66,plain,(
% 7.32/1.50    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f45,f43])).
% 7.32/1.50  
% 7.32/1.50  fof(f8,axiom,(
% 7.32/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f26,plain,(
% 7.32/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.32/1.50    inference(nnf_transformation,[],[f8])).
% 7.32/1.50  
% 7.32/1.50  fof(f27,plain,(
% 7.32/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.32/1.50    inference(rectify,[],[f26])).
% 7.32/1.50  
% 7.32/1.50  fof(f28,plain,(
% 7.32/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f29,plain,(
% 7.32/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.32/1.50  
% 7.32/1.50  fof(f46,plain,(
% 7.32/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.32/1.50    inference(cnf_transformation,[],[f29])).
% 7.32/1.50  
% 7.32/1.50  fof(f70,plain,(
% 7.32/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.32/1.50    inference(definition_unfolding,[],[f46,f65])).
% 7.32/1.50  
% 7.32/1.50  fof(f76,plain,(
% 7.32/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.32/1.50    inference(equality_resolution,[],[f70])).
% 7.32/1.50  
% 7.32/1.50  fof(f58,plain,(
% 7.32/1.50    sK2 != sK4 | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 7.32/1.50    inference(cnf_transformation,[],[f33])).
% 7.32/1.50  
% 7.32/1.50  fof(f72,plain,(
% 7.32/1.50    sK2 != sK4 | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 7.32/1.50    inference(definition_unfolding,[],[f58,f43,f65])).
% 7.32/1.50  
% 7.32/1.50  fof(f47,plain,(
% 7.32/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.32/1.50    inference(cnf_transformation,[],[f29])).
% 7.32/1.50  
% 7.32/1.50  fof(f69,plain,(
% 7.32/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.32/1.50    inference(definition_unfolding,[],[f47,f65])).
% 7.32/1.50  
% 7.32/1.50  fof(f74,plain,(
% 7.32/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.32/1.50    inference(equality_resolution,[],[f69])).
% 7.32/1.50  
% 7.32/1.50  fof(f75,plain,(
% 7.32/1.50    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.32/1.50    inference(equality_resolution,[],[f74])).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,X1)
% 7.32/1.50      | r2_hidden(X0,X2)
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19982,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_15,negated_conjecture,
% 7.32/1.50      ( ~ r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 7.32/1.50      | ~ r2_hidden(sK2,sK3)
% 7.32/1.50      | sK2 = sK4 ),
% 7.32/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19975,plain,
% 7.32/1.50      ( sK2 = sK4
% 7.32/1.50      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
% 7.32/1.50      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20123,plain,
% 7.32/1.50      ( sK4 = sK2
% 7.32/1.50      | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 7.32/1.50      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_19982,c_19975]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4112,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4108,plain,
% 7.32/1.50      ( sK2 = sK4
% 7.32/1.50      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
% 7.32/1.50      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4222,plain,
% 7.32/1.50      ( sK4 = sK2
% 7.32/1.50      | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 7.32/1.50      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4112,c_4108]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_17,negated_conjecture,
% 7.32/1.50      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 7.32/1.50      | r2_hidden(sK2,sK3) ),
% 7.32/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4106,plain,
% 7.32/1.50      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
% 7.32/1.50      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4,plain,
% 7.32/1.50      ( r2_hidden(X0,X1)
% 7.32/1.50      | r2_hidden(X0,X2)
% 7.32/1.50      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4111,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4214,plain,
% 7.32/1.50      ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 7.32/1.50      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4106,c_4111]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4272,plain,
% 7.32/1.50      ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 7.32/1.50      | sK4 = sK2 ),
% 7.32/1.50      inference(global_propositional_subsumption,[status(thm)],[c_4222,c_4214]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4273,plain,
% 7.32/1.50      ( sK4 = sK2
% 7.32/1.50      | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
% 7.32/1.50      inference(renaming,[status(thm)],[c_4272]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20191,plain,
% 7.32/1.50      ( r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 7.32/1.50      | sK4 = sK2 ),
% 7.32/1.50      inference(global_propositional_subsumption,
% 7.32/1.50                [status(thm)],
% 7.32/1.50                [c_20123,c_4273]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20192,plain,
% 7.32/1.50      ( sK4 = sK2
% 7.32/1.50      | r2_hidden(sK2,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
% 7.32/1.50      inference(renaming,[status(thm)],[c_20191]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_8,plain,
% 7.32/1.50      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19979,plain,
% 7.32/1.50      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_5,negated_conjecture,
% 7.32/1.50      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.32/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19980,plain,
% 7.32/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X2,X0) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20099,plain,
% 7.32/1.50      ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_19979,c_19980]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20147,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_19982,c_20099]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4109,plain,
% 7.32/1.50      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4110,plain,
% 7.32/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X2,X0) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4182,plain,
% 7.32/1.50      ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4109,c_4110]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4220,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4112,c_4182]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,X1)
% 7.32/1.50      | r2_hidden(X0,X2)
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4420,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_0,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X0) = X0 ),
% 7.32/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_9,plain,
% 7.32/1.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4609,plain,
% 7.32/1.50      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_10,plain,
% 7.32/1.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 7.32/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4414,plain,
% 7.32/1.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4416,plain,
% 7.32/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X2,X0) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4559,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4414,c_4416]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4915,plain,
% 7.32/1.50      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4609,c_4559]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_7837,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_4420,c_4915]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20229,plain,
% 7.32/1.50      ( r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.32/1.50      inference(global_propositional_subsumption,
% 7.32/1.50                [status(thm)],
% 7.32/1.50                [c_20147,c_4220,c_7837]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20230,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.32/1.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.32/1.50      inference(renaming,[status(thm)],[c_20229]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20236,plain,
% 7.32/1.50      ( sK4 = sK2
% 7.32/1.50      | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_20192,c_20230]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_14,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.32/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19976,plain,
% 7.32/1.50      ( X0 = X1
% 7.32/1.50      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20252,plain,
% 7.32/1.50      ( sK4 = sK2 ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_20236,c_19976]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_16,negated_conjecture,
% 7.32/1.50      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 7.32/1.50      | sK2 != sK4 ),
% 7.32/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19974,plain,
% 7.32/1.50      ( sK2 != sK4
% 7.32/1.50      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20279,plain,
% 7.32/1.50      ( sK2 != sK2
% 7.32/1.50      | r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.32/1.50      inference(demodulation,[status(thm)],[c_20252,c_19974]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20280,plain,
% 7.32/1.50      ( r2_hidden(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.32/1.50      inference(equality_resolution_simp,[status(thm)],[c_20279]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19978,plain,
% 7.32/1.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20062,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_19978,c_19980]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20293,plain,
% 7.32/1.50      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_20280,c_20062]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_13,plain,
% 7.32/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19977,plain,
% 7.32/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20307,plain,
% 7.32/1.50      ( $false ),
% 7.32/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_20293,c_19977]) ).
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  ------                               Statistics
% 7.32/1.50  
% 7.32/1.50  ------ Selected
% 7.32/1.50  
% 7.32/1.50  total_time:                             0.581
% 7.32/1.50  
%------------------------------------------------------------------------------
