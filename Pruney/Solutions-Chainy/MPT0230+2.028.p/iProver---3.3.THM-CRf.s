%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:45 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  168 (4333 expanded)
%              Number of clauses        :   88 (1268 expanded)
%              Number of leaves         :   22 (1159 expanded)
%              Depth                    :   26
%              Number of atoms          :  408 (5882 expanded)
%              Number of equality atoms :  321 (4569 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f104,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f105,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f75,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f48,f68,f75])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f63,f68,f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK2 != sK4
      & sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( sK2 != sK4
    & sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f38])).

fof(f71,plain,(
    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f71,f75,f74])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f45,f45])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f106,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f64,f68,f68])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f109,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f94])).

fof(f110,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f109])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f73,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1855,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_22,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3463,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X1,X2,X0,X3) ),
    inference(superposition,[status(thm)],[c_22,c_1])).

cnf(c_11316,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X0,X1,X3) ),
    inference(superposition,[status(thm)],[c_1,c_3463])).

cnf(c_11388,plain,
    ( k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_11316,c_22])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_216,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_217,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_2665,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_22,c_217])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2760,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2665,c_0])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2599,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_2761,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_2760,c_2599])).

cnf(c_3459,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK4,sK3,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_2761,c_1])).

cnf(c_11599,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK4,sK4,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_11388,c_3459])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_209,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_210,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_4039,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_210,c_0])).

cnf(c_4041,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4039,c_6])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2662,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_6353,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_4041,c_2662])).

cnf(c_4659,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4041,c_2])).

cnf(c_4042,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4041,c_210])).

cnf(c_4660,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4659,c_4042])).

cnf(c_6380,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6353,c_4660])).

cnf(c_2663,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_4793,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4041,c_2663])).

cnf(c_4799,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_4793,c_6,c_4042])).

cnf(c_4803,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_4799])).

cnf(c_6068,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4799,c_4803])).

cnf(c_6119,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6068,c_4799])).

cnf(c_6120,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_6119,c_4041,c_4042])).

cnf(c_6381,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6380,c_2599,c_4042,c_6120])).

cnf(c_11600,plain,
    ( k2_enumset1(sK4,sK4,sK2,sK3) = k2_enumset1(sK4,sK4,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_11599,c_6,c_6381])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1854,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11810,plain,
    ( sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11600,c_1854])).

cnf(c_4655,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK4,sK4,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2761,c_4041])).

cnf(c_4664,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK4,sK4,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4655,c_2761])).

cnf(c_5329,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_4664,c_2])).

cnf(c_2600,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_217,c_0])).

cnf(c_2605,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_2599,c_2600])).

cnf(c_2848,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK4,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_22,c_2605])).

cnf(c_4033,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK4,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2848,c_210])).

cnf(c_4656,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK4,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_2848,c_4041])).

cnf(c_4663,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK4,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4656,c_2848])).

cnf(c_4670,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4033,c_4663])).

cnf(c_4806,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK4,sK4,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2761,c_4799])).

cnf(c_5330,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k2_enumset1(sK4,sK4,sK3,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5329,c_4670,c_4806])).

cnf(c_11796,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK2,sK3),k2_enumset1(sK4,sK4,sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11600,c_5330])).

cnf(c_2601,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_2604,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2601,c_4])).

cnf(c_12305,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK2,sK3),k1_xboole_0) = k2_enumset1(sK4,sK4,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_11796,c_2604])).

cnf(c_11799,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK2,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_11600,c_2761])).

cnf(c_11800,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11799,c_6381])).

cnf(c_11836,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK2,sK3),k1_xboole_0) = k2_enumset1(sK2,sK3,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_11800,c_3463])).

cnf(c_12306,plain,
    ( k2_enumset1(sK2,sK3,sK4,sK2) = k2_enumset1(sK4,sK4,sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_12305,c_11836])).

cnf(c_25739,plain,
    ( sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k2_enumset1(sK2,sK3,sK4,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11810,c_12306])).

cnf(c_23,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3465,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X2,X1,X0,X3) ),
    inference(superposition,[status(thm)],[c_23,c_1])).

cnf(c_18217,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(superposition,[status(thm)],[c_3465,c_1])).

cnf(c_2758,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_23,c_22])).

cnf(c_11823,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK4,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2758,c_11800])).

cnf(c_12317,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK4,sK3),k1_xboole_0) = k2_enumset1(sK4,sK3,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_11823,c_3463])).

cnf(c_12336,plain,
    ( k2_enumset1(sK4,sK3,sK2,sK2) = k2_enumset1(sK2,sK2,sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_12317,c_6])).

cnf(c_18350,plain,
    ( k2_enumset1(sK2,sK3,sK4,sK2) = k2_enumset1(sK2,sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_18217,c_12336])).

cnf(c_25740,plain,
    ( sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k2_enumset1(sK2,sK2,sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25739,c_18350])).

cnf(c_25747,plain,
    ( sK3 = sK2
    | sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_1855,c_25740])).

cnf(c_1644,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1890,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_1891,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_1882,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_1883,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_36,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_33,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25747,c_1891,c_1883,c_36,c_33,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:48:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.61/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.48  
% 7.61/1.48  ------  iProver source info
% 7.61/1.48  
% 7.61/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.48  git: non_committed_changes: false
% 7.61/1.48  git: last_make_outside_of_git: false
% 7.61/1.48  
% 7.61/1.48  ------ 
% 7.61/1.48  
% 7.61/1.48  ------ Input Options
% 7.61/1.48  
% 7.61/1.48  --out_options                           all
% 7.61/1.48  --tptp_safe_out                         true
% 7.61/1.48  --problem_path                          ""
% 7.61/1.48  --include_path                          ""
% 7.61/1.48  --clausifier                            res/vclausify_rel
% 7.61/1.48  --clausifier_options                    ""
% 7.61/1.48  --stdin                                 false
% 7.61/1.48  --stats_out                             all
% 7.61/1.48  
% 7.61/1.48  ------ General Options
% 7.61/1.48  
% 7.61/1.48  --fof                                   false
% 7.61/1.48  --time_out_real                         305.
% 7.61/1.48  --time_out_virtual                      -1.
% 7.61/1.48  --symbol_type_check                     false
% 7.61/1.48  --clausify_out                          false
% 7.61/1.48  --sig_cnt_out                           false
% 7.61/1.48  --trig_cnt_out                          false
% 7.61/1.48  --trig_cnt_out_tolerance                1.
% 7.61/1.48  --trig_cnt_out_sk_spl                   false
% 7.61/1.48  --abstr_cl_out                          false
% 7.61/1.48  
% 7.61/1.48  ------ Global Options
% 7.61/1.48  
% 7.61/1.48  --schedule                              default
% 7.61/1.48  --add_important_lit                     false
% 7.61/1.48  --prop_solver_per_cl                    1000
% 7.61/1.48  --min_unsat_core                        false
% 7.61/1.48  --soft_assumptions                      false
% 7.61/1.48  --soft_lemma_size                       3
% 7.61/1.48  --prop_impl_unit_size                   0
% 7.61/1.48  --prop_impl_unit                        []
% 7.61/1.48  --share_sel_clauses                     true
% 7.61/1.48  --reset_solvers                         false
% 7.61/1.48  --bc_imp_inh                            [conj_cone]
% 7.61/1.48  --conj_cone_tolerance                   3.
% 7.61/1.48  --extra_neg_conj                        none
% 7.61/1.48  --large_theory_mode                     true
% 7.61/1.48  --prolific_symb_bound                   200
% 7.61/1.48  --lt_threshold                          2000
% 7.61/1.48  --clause_weak_htbl                      true
% 7.61/1.48  --gc_record_bc_elim                     false
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing Options
% 7.61/1.48  
% 7.61/1.48  --preprocessing_flag                    true
% 7.61/1.48  --time_out_prep_mult                    0.1
% 7.61/1.48  --splitting_mode                        input
% 7.61/1.48  --splitting_grd                         true
% 7.61/1.48  --splitting_cvd                         false
% 7.61/1.48  --splitting_cvd_svl                     false
% 7.61/1.48  --splitting_nvd                         32
% 7.61/1.48  --sub_typing                            true
% 7.61/1.48  --prep_gs_sim                           true
% 7.61/1.48  --prep_unflatten                        true
% 7.61/1.48  --prep_res_sim                          true
% 7.61/1.48  --prep_upred                            true
% 7.61/1.48  --prep_sem_filter                       exhaustive
% 7.61/1.48  --prep_sem_filter_out                   false
% 7.61/1.48  --pred_elim                             true
% 7.61/1.48  --res_sim_input                         true
% 7.61/1.48  --eq_ax_congr_red                       true
% 7.61/1.48  --pure_diseq_elim                       true
% 7.61/1.48  --brand_transform                       false
% 7.61/1.48  --non_eq_to_eq                          false
% 7.61/1.48  --prep_def_merge                        true
% 7.61/1.48  --prep_def_merge_prop_impl              false
% 7.61/1.48  --prep_def_merge_mbd                    true
% 7.61/1.48  --prep_def_merge_tr_red                 false
% 7.61/1.48  --prep_def_merge_tr_cl                  false
% 7.61/1.48  --smt_preprocessing                     true
% 7.61/1.48  --smt_ac_axioms                         fast
% 7.61/1.48  --preprocessed_out                      false
% 7.61/1.48  --preprocessed_stats                    false
% 7.61/1.48  
% 7.61/1.48  ------ Abstraction refinement Options
% 7.61/1.48  
% 7.61/1.48  --abstr_ref                             []
% 7.61/1.48  --abstr_ref_prep                        false
% 7.61/1.48  --abstr_ref_until_sat                   false
% 7.61/1.48  --abstr_ref_sig_restrict                funpre
% 7.61/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.61/1.48  --abstr_ref_under                       []
% 7.61/1.48  
% 7.61/1.48  ------ SAT Options
% 7.61/1.48  
% 7.61/1.48  --sat_mode                              false
% 7.61/1.48  --sat_fm_restart_options                ""
% 7.61/1.48  --sat_gr_def                            false
% 7.61/1.48  --sat_epr_types                         true
% 7.61/1.48  --sat_non_cyclic_types                  false
% 7.61/1.48  --sat_finite_models                     false
% 7.61/1.48  --sat_fm_lemmas                         false
% 7.61/1.48  --sat_fm_prep                           false
% 7.61/1.48  --sat_fm_uc_incr                        true
% 7.61/1.48  --sat_out_model                         small
% 7.61/1.48  --sat_out_clauses                       false
% 7.61/1.48  
% 7.61/1.48  ------ QBF Options
% 7.61/1.48  
% 7.61/1.48  --qbf_mode                              false
% 7.61/1.48  --qbf_elim_univ                         false
% 7.61/1.48  --qbf_dom_inst                          none
% 7.61/1.48  --qbf_dom_pre_inst                      false
% 7.61/1.48  --qbf_sk_in                             false
% 7.61/1.48  --qbf_pred_elim                         true
% 7.61/1.48  --qbf_split                             512
% 7.61/1.48  
% 7.61/1.48  ------ BMC1 Options
% 7.61/1.48  
% 7.61/1.48  --bmc1_incremental                      false
% 7.61/1.48  --bmc1_axioms                           reachable_all
% 7.61/1.48  --bmc1_min_bound                        0
% 7.61/1.48  --bmc1_max_bound                        -1
% 7.61/1.48  --bmc1_max_bound_default                -1
% 7.61/1.48  --bmc1_symbol_reachability              true
% 7.61/1.48  --bmc1_property_lemmas                  false
% 7.61/1.48  --bmc1_k_induction                      false
% 7.61/1.48  --bmc1_non_equiv_states                 false
% 7.61/1.48  --bmc1_deadlock                         false
% 7.61/1.48  --bmc1_ucm                              false
% 7.61/1.48  --bmc1_add_unsat_core                   none
% 7.61/1.48  --bmc1_unsat_core_children              false
% 7.61/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.61/1.48  --bmc1_out_stat                         full
% 7.61/1.48  --bmc1_ground_init                      false
% 7.61/1.48  --bmc1_pre_inst_next_state              false
% 7.61/1.48  --bmc1_pre_inst_state                   false
% 7.61/1.48  --bmc1_pre_inst_reach_state             false
% 7.61/1.48  --bmc1_out_unsat_core                   false
% 7.61/1.48  --bmc1_aig_witness_out                  false
% 7.61/1.48  --bmc1_verbose                          false
% 7.61/1.48  --bmc1_dump_clauses_tptp                false
% 7.61/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.61/1.48  --bmc1_dump_file                        -
% 7.61/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.61/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.61/1.48  --bmc1_ucm_extend_mode                  1
% 7.61/1.48  --bmc1_ucm_init_mode                    2
% 7.61/1.48  --bmc1_ucm_cone_mode                    none
% 7.61/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.61/1.48  --bmc1_ucm_relax_model                  4
% 7.61/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.61/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.61/1.48  --bmc1_ucm_layered_model                none
% 7.61/1.48  --bmc1_ucm_max_lemma_size               10
% 7.61/1.48  
% 7.61/1.48  ------ AIG Options
% 7.61/1.48  
% 7.61/1.48  --aig_mode                              false
% 7.61/1.48  
% 7.61/1.48  ------ Instantiation Options
% 7.61/1.48  
% 7.61/1.48  --instantiation_flag                    true
% 7.61/1.48  --inst_sos_flag                         true
% 7.61/1.48  --inst_sos_phase                        true
% 7.61/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel_side                     num_symb
% 7.61/1.48  --inst_solver_per_active                1400
% 7.61/1.48  --inst_solver_calls_frac                1.
% 7.61/1.48  --inst_passive_queue_type               priority_queues
% 7.61/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.61/1.48  --inst_passive_queues_freq              [25;2]
% 7.61/1.48  --inst_dismatching                      true
% 7.61/1.48  --inst_eager_unprocessed_to_passive     true
% 7.61/1.48  --inst_prop_sim_given                   true
% 7.61/1.48  --inst_prop_sim_new                     false
% 7.61/1.48  --inst_subs_new                         false
% 7.61/1.48  --inst_eq_res_simp                      false
% 7.61/1.48  --inst_subs_given                       false
% 7.61/1.48  --inst_orphan_elimination               true
% 7.61/1.48  --inst_learning_loop_flag               true
% 7.61/1.48  --inst_learning_start                   3000
% 7.61/1.48  --inst_learning_factor                  2
% 7.61/1.48  --inst_start_prop_sim_after_learn       3
% 7.61/1.48  --inst_sel_renew                        solver
% 7.61/1.48  --inst_lit_activity_flag                true
% 7.61/1.48  --inst_restr_to_given                   false
% 7.61/1.48  --inst_activity_threshold               500
% 7.61/1.48  --inst_out_proof                        true
% 7.61/1.48  
% 7.61/1.48  ------ Resolution Options
% 7.61/1.48  
% 7.61/1.48  --resolution_flag                       true
% 7.61/1.48  --res_lit_sel                           adaptive
% 7.61/1.48  --res_lit_sel_side                      none
% 7.61/1.48  --res_ordering                          kbo
% 7.61/1.48  --res_to_prop_solver                    active
% 7.61/1.48  --res_prop_simpl_new                    false
% 7.61/1.48  --res_prop_simpl_given                  true
% 7.61/1.48  --res_passive_queue_type                priority_queues
% 7.61/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.61/1.48  --res_passive_queues_freq               [15;5]
% 7.61/1.48  --res_forward_subs                      full
% 7.61/1.48  --res_backward_subs                     full
% 7.61/1.48  --res_forward_subs_resolution           true
% 7.61/1.48  --res_backward_subs_resolution          true
% 7.61/1.48  --res_orphan_elimination                true
% 7.61/1.48  --res_time_limit                        2.
% 7.61/1.48  --res_out_proof                         true
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Options
% 7.61/1.48  
% 7.61/1.48  --superposition_flag                    true
% 7.61/1.48  --sup_passive_queue_type                priority_queues
% 7.61/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.61/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.61/1.48  --demod_completeness_check              fast
% 7.61/1.48  --demod_use_ground                      true
% 7.61/1.48  --sup_to_prop_solver                    passive
% 7.61/1.48  --sup_prop_simpl_new                    true
% 7.61/1.48  --sup_prop_simpl_given                  true
% 7.61/1.48  --sup_fun_splitting                     true
% 7.61/1.48  --sup_smt_interval                      50000
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Simplification Setup
% 7.61/1.48  
% 7.61/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.61/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.61/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.61/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.61/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.61/1.48  --sup_immed_triv                        [TrivRules]
% 7.61/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_immed_bw_main                     []
% 7.61/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.61/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.61/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_input_bw                          []
% 7.61/1.48  
% 7.61/1.48  ------ Combination Options
% 7.61/1.48  
% 7.61/1.48  --comb_res_mult                         3
% 7.61/1.48  --comb_sup_mult                         2
% 7.61/1.48  --comb_inst_mult                        10
% 7.61/1.48  
% 7.61/1.48  ------ Debug Options
% 7.61/1.48  
% 7.61/1.48  --dbg_backtrace                         false
% 7.61/1.48  --dbg_dump_prop_clauses                 false
% 7.61/1.48  --dbg_dump_prop_clauses_file            -
% 7.61/1.48  --dbg_out_stat                          false
% 7.61/1.48  ------ Parsing...
% 7.61/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  ------ Proving...
% 7.61/1.48  ------ Problem Properties 
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  clauses                                 27
% 7.61/1.48  conjectures                             2
% 7.61/1.48  EPR                                     2
% 7.61/1.48  Horn                                    23
% 7.61/1.48  unary                                   18
% 7.61/1.48  binary                                  0
% 7.61/1.48  lits                                    49
% 7.61/1.48  lits eq                                 35
% 7.61/1.48  fd_pure                                 0
% 7.61/1.48  fd_pseudo                               0
% 7.61/1.48  fd_cond                                 0
% 7.61/1.48  fd_pseudo_cond                          7
% 7.61/1.48  AC symbols                              0
% 7.61/1.48  
% 7.61/1.48  ------ Schedule dynamic 5 is on 
% 7.61/1.48  
% 7.61/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ 
% 7.61/1.48  Current options:
% 7.61/1.48  ------ 
% 7.61/1.48  
% 7.61/1.48  ------ Input Options
% 7.61/1.48  
% 7.61/1.48  --out_options                           all
% 7.61/1.48  --tptp_safe_out                         true
% 7.61/1.48  --problem_path                          ""
% 7.61/1.48  --include_path                          ""
% 7.61/1.48  --clausifier                            res/vclausify_rel
% 7.61/1.48  --clausifier_options                    ""
% 7.61/1.48  --stdin                                 false
% 7.61/1.48  --stats_out                             all
% 7.61/1.48  
% 7.61/1.48  ------ General Options
% 7.61/1.48  
% 7.61/1.48  --fof                                   false
% 7.61/1.48  --time_out_real                         305.
% 7.61/1.48  --time_out_virtual                      -1.
% 7.61/1.48  --symbol_type_check                     false
% 7.61/1.48  --clausify_out                          false
% 7.61/1.48  --sig_cnt_out                           false
% 7.61/1.48  --trig_cnt_out                          false
% 7.61/1.48  --trig_cnt_out_tolerance                1.
% 7.61/1.48  --trig_cnt_out_sk_spl                   false
% 7.61/1.48  --abstr_cl_out                          false
% 7.61/1.48  
% 7.61/1.48  ------ Global Options
% 7.61/1.48  
% 7.61/1.48  --schedule                              default
% 7.61/1.48  --add_important_lit                     false
% 7.61/1.48  --prop_solver_per_cl                    1000
% 7.61/1.48  --min_unsat_core                        false
% 7.61/1.48  --soft_assumptions                      false
% 7.61/1.48  --soft_lemma_size                       3
% 7.61/1.48  --prop_impl_unit_size                   0
% 7.61/1.48  --prop_impl_unit                        []
% 7.61/1.48  --share_sel_clauses                     true
% 7.61/1.48  --reset_solvers                         false
% 7.61/1.48  --bc_imp_inh                            [conj_cone]
% 7.61/1.48  --conj_cone_tolerance                   3.
% 7.61/1.48  --extra_neg_conj                        none
% 7.61/1.48  --large_theory_mode                     true
% 7.61/1.48  --prolific_symb_bound                   200
% 7.61/1.48  --lt_threshold                          2000
% 7.61/1.48  --clause_weak_htbl                      true
% 7.61/1.48  --gc_record_bc_elim                     false
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing Options
% 7.61/1.48  
% 7.61/1.48  --preprocessing_flag                    true
% 7.61/1.48  --time_out_prep_mult                    0.1
% 7.61/1.48  --splitting_mode                        input
% 7.61/1.48  --splitting_grd                         true
% 7.61/1.48  --splitting_cvd                         false
% 7.61/1.48  --splitting_cvd_svl                     false
% 7.61/1.48  --splitting_nvd                         32
% 7.61/1.48  --sub_typing                            true
% 7.61/1.48  --prep_gs_sim                           true
% 7.61/1.48  --prep_unflatten                        true
% 7.61/1.48  --prep_res_sim                          true
% 7.61/1.48  --prep_upred                            true
% 7.61/1.48  --prep_sem_filter                       exhaustive
% 7.61/1.48  --prep_sem_filter_out                   false
% 7.61/1.48  --pred_elim                             true
% 7.61/1.48  --res_sim_input                         true
% 7.61/1.48  --eq_ax_congr_red                       true
% 7.61/1.48  --pure_diseq_elim                       true
% 7.61/1.48  --brand_transform                       false
% 7.61/1.48  --non_eq_to_eq                          false
% 7.61/1.48  --prep_def_merge                        true
% 7.61/1.48  --prep_def_merge_prop_impl              false
% 7.61/1.48  --prep_def_merge_mbd                    true
% 7.61/1.48  --prep_def_merge_tr_red                 false
% 7.61/1.48  --prep_def_merge_tr_cl                  false
% 7.61/1.48  --smt_preprocessing                     true
% 7.61/1.48  --smt_ac_axioms                         fast
% 7.61/1.48  --preprocessed_out                      false
% 7.61/1.48  --preprocessed_stats                    false
% 7.61/1.48  
% 7.61/1.48  ------ Abstraction refinement Options
% 7.61/1.48  
% 7.61/1.48  --abstr_ref                             []
% 7.61/1.48  --abstr_ref_prep                        false
% 7.61/1.48  --abstr_ref_until_sat                   false
% 7.61/1.48  --abstr_ref_sig_restrict                funpre
% 7.61/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.61/1.48  --abstr_ref_under                       []
% 7.61/1.48  
% 7.61/1.48  ------ SAT Options
% 7.61/1.48  
% 7.61/1.48  --sat_mode                              false
% 7.61/1.48  --sat_fm_restart_options                ""
% 7.61/1.48  --sat_gr_def                            false
% 7.61/1.48  --sat_epr_types                         true
% 7.61/1.48  --sat_non_cyclic_types                  false
% 7.61/1.48  --sat_finite_models                     false
% 7.61/1.48  --sat_fm_lemmas                         false
% 7.61/1.48  --sat_fm_prep                           false
% 7.61/1.48  --sat_fm_uc_incr                        true
% 7.61/1.48  --sat_out_model                         small
% 7.61/1.48  --sat_out_clauses                       false
% 7.61/1.48  
% 7.61/1.48  ------ QBF Options
% 7.61/1.48  
% 7.61/1.48  --qbf_mode                              false
% 7.61/1.48  --qbf_elim_univ                         false
% 7.61/1.48  --qbf_dom_inst                          none
% 7.61/1.48  --qbf_dom_pre_inst                      false
% 7.61/1.48  --qbf_sk_in                             false
% 7.61/1.48  --qbf_pred_elim                         true
% 7.61/1.48  --qbf_split                             512
% 7.61/1.48  
% 7.61/1.48  ------ BMC1 Options
% 7.61/1.48  
% 7.61/1.48  --bmc1_incremental                      false
% 7.61/1.48  --bmc1_axioms                           reachable_all
% 7.61/1.48  --bmc1_min_bound                        0
% 7.61/1.48  --bmc1_max_bound                        -1
% 7.61/1.48  --bmc1_max_bound_default                -1
% 7.61/1.48  --bmc1_symbol_reachability              true
% 7.61/1.48  --bmc1_property_lemmas                  false
% 7.61/1.48  --bmc1_k_induction                      false
% 7.61/1.48  --bmc1_non_equiv_states                 false
% 7.61/1.48  --bmc1_deadlock                         false
% 7.61/1.48  --bmc1_ucm                              false
% 7.61/1.48  --bmc1_add_unsat_core                   none
% 7.61/1.48  --bmc1_unsat_core_children              false
% 7.61/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.61/1.48  --bmc1_out_stat                         full
% 7.61/1.48  --bmc1_ground_init                      false
% 7.61/1.48  --bmc1_pre_inst_next_state              false
% 7.61/1.48  --bmc1_pre_inst_state                   false
% 7.61/1.48  --bmc1_pre_inst_reach_state             false
% 7.61/1.48  --bmc1_out_unsat_core                   false
% 7.61/1.48  --bmc1_aig_witness_out                  false
% 7.61/1.48  --bmc1_verbose                          false
% 7.61/1.48  --bmc1_dump_clauses_tptp                false
% 7.61/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.61/1.48  --bmc1_dump_file                        -
% 7.61/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.61/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.61/1.48  --bmc1_ucm_extend_mode                  1
% 7.61/1.48  --bmc1_ucm_init_mode                    2
% 7.61/1.48  --bmc1_ucm_cone_mode                    none
% 7.61/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.61/1.48  --bmc1_ucm_relax_model                  4
% 7.61/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.61/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.61/1.48  --bmc1_ucm_layered_model                none
% 7.61/1.48  --bmc1_ucm_max_lemma_size               10
% 7.61/1.48  
% 7.61/1.48  ------ AIG Options
% 7.61/1.48  
% 7.61/1.48  --aig_mode                              false
% 7.61/1.48  
% 7.61/1.48  ------ Instantiation Options
% 7.61/1.48  
% 7.61/1.48  --instantiation_flag                    true
% 7.61/1.48  --inst_sos_flag                         true
% 7.61/1.48  --inst_sos_phase                        true
% 7.61/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel_side                     none
% 7.61/1.48  --inst_solver_per_active                1400
% 7.61/1.48  --inst_solver_calls_frac                1.
% 7.61/1.48  --inst_passive_queue_type               priority_queues
% 7.61/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.61/1.48  --inst_passive_queues_freq              [25;2]
% 7.61/1.48  --inst_dismatching                      true
% 7.61/1.48  --inst_eager_unprocessed_to_passive     true
% 7.61/1.48  --inst_prop_sim_given                   true
% 7.61/1.48  --inst_prop_sim_new                     false
% 7.61/1.48  --inst_subs_new                         false
% 7.61/1.48  --inst_eq_res_simp                      false
% 7.61/1.48  --inst_subs_given                       false
% 7.61/1.48  --inst_orphan_elimination               true
% 7.61/1.48  --inst_learning_loop_flag               true
% 7.61/1.48  --inst_learning_start                   3000
% 7.61/1.48  --inst_learning_factor                  2
% 7.61/1.48  --inst_start_prop_sim_after_learn       3
% 7.61/1.48  --inst_sel_renew                        solver
% 7.61/1.48  --inst_lit_activity_flag                true
% 7.61/1.48  --inst_restr_to_given                   false
% 7.61/1.48  --inst_activity_threshold               500
% 7.61/1.48  --inst_out_proof                        true
% 7.61/1.48  
% 7.61/1.48  ------ Resolution Options
% 7.61/1.48  
% 7.61/1.48  --resolution_flag                       false
% 7.61/1.48  --res_lit_sel                           adaptive
% 7.61/1.48  --res_lit_sel_side                      none
% 7.61/1.48  --res_ordering                          kbo
% 7.61/1.48  --res_to_prop_solver                    active
% 7.61/1.48  --res_prop_simpl_new                    false
% 7.61/1.48  --res_prop_simpl_given                  true
% 7.61/1.48  --res_passive_queue_type                priority_queues
% 7.61/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.61/1.48  --res_passive_queues_freq               [15;5]
% 7.61/1.48  --res_forward_subs                      full
% 7.61/1.48  --res_backward_subs                     full
% 7.61/1.48  --res_forward_subs_resolution           true
% 7.61/1.48  --res_backward_subs_resolution          true
% 7.61/1.48  --res_orphan_elimination                true
% 7.61/1.48  --res_time_limit                        2.
% 7.61/1.48  --res_out_proof                         true
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Options
% 7.61/1.48  
% 7.61/1.48  --superposition_flag                    true
% 7.61/1.48  --sup_passive_queue_type                priority_queues
% 7.61/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.61/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.61/1.48  --demod_completeness_check              fast
% 7.61/1.48  --demod_use_ground                      true
% 7.61/1.48  --sup_to_prop_solver                    passive
% 7.61/1.48  --sup_prop_simpl_new                    true
% 7.61/1.48  --sup_prop_simpl_given                  true
% 7.61/1.48  --sup_fun_splitting                     true
% 7.61/1.48  --sup_smt_interval                      50000
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Simplification Setup
% 7.61/1.48  
% 7.61/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.61/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.61/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.61/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.61/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.61/1.48  --sup_immed_triv                        [TrivRules]
% 7.61/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_immed_bw_main                     []
% 7.61/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.61/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.61/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_input_bw                          []
% 7.61/1.48  
% 7.61/1.48  ------ Combination Options
% 7.61/1.48  
% 7.61/1.48  --comb_res_mult                         3
% 7.61/1.48  --comb_sup_mult                         2
% 7.61/1.48  --comb_inst_mult                        10
% 7.61/1.48  
% 7.61/1.48  ------ Debug Options
% 7.61/1.48  
% 7.61/1.48  --dbg_backtrace                         false
% 7.61/1.48  --dbg_dump_prop_clauses                 false
% 7.61/1.48  --dbg_dump_prop_clauses_file            -
% 7.61/1.48  --dbg_out_stat                          false
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  % SZS status Theorem for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  fof(f10,axiom,(
% 7.61/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f26,plain,(
% 7.61/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.61/1.48    inference(ennf_transformation,[],[f10])).
% 7.61/1.48  
% 7.61/1.48  fof(f28,plain,(
% 7.61/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.61/1.48    inference(nnf_transformation,[],[f26])).
% 7.61/1.48  
% 7.61/1.48  fof(f29,plain,(
% 7.61/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.61/1.48    inference(flattening,[],[f28])).
% 7.61/1.48  
% 7.61/1.48  fof(f30,plain,(
% 7.61/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.61/1.48    inference(rectify,[],[f29])).
% 7.61/1.48  
% 7.61/1.48  fof(f31,plain,(
% 7.61/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f32,plain,(
% 7.61/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.61/1.48  
% 7.61/1.48  fof(f50,plain,(
% 7.61/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.61/1.48    inference(cnf_transformation,[],[f32])).
% 7.61/1.48  
% 7.61/1.48  fof(f17,axiom,(
% 7.61/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f68,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f17])).
% 7.61/1.48  
% 7.61/1.48  fof(f88,plain,(
% 7.61/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.61/1.48    inference(definition_unfolding,[],[f50,f68])).
% 7.61/1.48  
% 7.61/1.48  fof(f104,plain,(
% 7.61/1.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 7.61/1.48    inference(equality_resolution,[],[f88])).
% 7.61/1.48  
% 7.61/1.48  fof(f105,plain,(
% 7.61/1.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 7.61/1.48    inference(equality_resolution,[],[f104])).
% 7.61/1.48  
% 7.61/1.48  fof(f14,axiom,(
% 7.61/1.48    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f65,plain,(
% 7.61/1.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f14])).
% 7.61/1.48  
% 7.61/1.48  fof(f9,axiom,(
% 7.61/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f48,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f9])).
% 7.61/1.48  
% 7.61/1.48  fof(f15,axiom,(
% 7.61/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f66,plain,(
% 7.61/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f15])).
% 7.61/1.48  
% 7.61/1.48  fof(f16,axiom,(
% 7.61/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f67,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f16])).
% 7.61/1.48  
% 7.61/1.48  fof(f74,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f67,f68])).
% 7.61/1.48  
% 7.61/1.48  fof(f75,plain,(
% 7.61/1.48    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f66,f74])).
% 7.61/1.48  
% 7.61/1.48  fof(f77,plain,(
% 7.61/1.48    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f65,f48,f68,f75])).
% 7.61/1.48  
% 7.61/1.48  fof(f12,axiom,(
% 7.61/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f63,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f12])).
% 7.61/1.48  
% 7.61/1.48  fof(f96,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f63,f68,f68])).
% 7.61/1.48  
% 7.61/1.48  fof(f5,axiom,(
% 7.61/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f25,plain,(
% 7.61/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.61/1.48    inference(ennf_transformation,[],[f5])).
% 7.61/1.48  
% 7.61/1.48  fof(f44,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f25])).
% 7.61/1.48  
% 7.61/1.48  fof(f6,axiom,(
% 7.61/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f45,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.61/1.48    inference(cnf_transformation,[],[f6])).
% 7.61/1.48  
% 7.61/1.48  fof(f81,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f44,f45])).
% 7.61/1.48  
% 7.61/1.48  fof(f20,conjecture,(
% 7.61/1.48    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f21,negated_conjecture,(
% 7.61/1.48    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.61/1.48    inference(negated_conjecture,[],[f20])).
% 7.61/1.48  
% 7.61/1.48  fof(f27,plain,(
% 7.61/1.48    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.61/1.48    inference(ennf_transformation,[],[f21])).
% 7.61/1.48  
% 7.61/1.48  fof(f38,plain,(
% 7.61/1.48    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f39,plain,(
% 7.61/1.48    sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f38])).
% 7.61/1.48  
% 7.61/1.48  fof(f71,plain,(
% 7.61/1.48    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 7.61/1.48    inference(cnf_transformation,[],[f39])).
% 7.61/1.48  
% 7.61/1.48  fof(f99,plain,(
% 7.61/1.48    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))),
% 7.61/1.48    inference(definition_unfolding,[],[f71,f75,f74])).
% 7.61/1.48  
% 7.61/1.48  fof(f4,axiom,(
% 7.61/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f43,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.61/1.48    inference(cnf_transformation,[],[f4])).
% 7.61/1.48  
% 7.61/1.48  fof(f76,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.61/1.48    inference(definition_unfolding,[],[f43,f45])).
% 7.61/1.48  
% 7.61/1.48  fof(f3,axiom,(
% 7.61/1.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f22,plain,(
% 7.61/1.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.61/1.48    inference(rectify,[],[f3])).
% 7.61/1.48  
% 7.61/1.48  fof(f42,plain,(
% 7.61/1.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.61/1.48    inference(cnf_transformation,[],[f22])).
% 7.61/1.48  
% 7.61/1.48  fof(f80,plain,(
% 7.61/1.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.61/1.48    inference(definition_unfolding,[],[f42,f45])).
% 7.61/1.48  
% 7.61/1.48  fof(f7,axiom,(
% 7.61/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f46,plain,(
% 7.61/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.61/1.48    inference(cnf_transformation,[],[f7])).
% 7.61/1.48  
% 7.61/1.48  fof(f2,axiom,(
% 7.61/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f23,plain,(
% 7.61/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.61/1.48    inference(unused_predicate_definition_removal,[],[f2])).
% 7.61/1.48  
% 7.61/1.48  fof(f24,plain,(
% 7.61/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 7.61/1.48    inference(ennf_transformation,[],[f23])).
% 7.61/1.48  
% 7.61/1.48  fof(f41,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f24])).
% 7.61/1.48  
% 7.61/1.48  fof(f79,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f41,f45])).
% 7.61/1.48  
% 7.61/1.48  fof(f8,axiom,(
% 7.61/1.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f47,plain,(
% 7.61/1.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f8])).
% 7.61/1.48  
% 7.61/1.48  fof(f1,axiom,(
% 7.61/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f40,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f1])).
% 7.61/1.48  
% 7.61/1.48  fof(f78,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.61/1.48    inference(definition_unfolding,[],[f40,f45,f45])).
% 7.61/1.48  
% 7.61/1.48  fof(f49,plain,(
% 7.61/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.61/1.48    inference(cnf_transformation,[],[f32])).
% 7.61/1.48  
% 7.61/1.48  fof(f89,plain,(
% 7.61/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.61/1.48    inference(definition_unfolding,[],[f49,f68])).
% 7.61/1.48  
% 7.61/1.48  fof(f106,plain,(
% 7.61/1.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 7.61/1.48    inference(equality_resolution,[],[f89])).
% 7.61/1.48  
% 7.61/1.48  fof(f13,axiom,(
% 7.61/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f64,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f13])).
% 7.61/1.48  
% 7.61/1.48  fof(f97,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f64,f68,f68])).
% 7.61/1.48  
% 7.61/1.48  fof(f11,axiom,(
% 7.61/1.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f33,plain,(
% 7.61/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.48    inference(nnf_transformation,[],[f11])).
% 7.61/1.48  
% 7.61/1.48  fof(f34,plain,(
% 7.61/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.48    inference(flattening,[],[f33])).
% 7.61/1.48  
% 7.61/1.48  fof(f35,plain,(
% 7.61/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.48    inference(rectify,[],[f34])).
% 7.61/1.48  
% 7.61/1.48  fof(f36,plain,(
% 7.61/1.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f37,plain,(
% 7.61/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f58,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.61/1.48    inference(cnf_transformation,[],[f37])).
% 7.61/1.48  
% 7.61/1.48  fof(f94,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.61/1.48    inference(definition_unfolding,[],[f58,f74])).
% 7.61/1.48  
% 7.61/1.48  fof(f109,plain,(
% 7.61/1.48    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.61/1.48    inference(equality_resolution,[],[f94])).
% 7.61/1.48  
% 7.61/1.48  fof(f110,plain,(
% 7.61/1.48    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.61/1.48    inference(equality_resolution,[],[f109])).
% 7.61/1.48  
% 7.61/1.48  fof(f57,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.61/1.48    inference(cnf_transformation,[],[f37])).
% 7.61/1.48  
% 7.61/1.48  fof(f95,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.61/1.48    inference(definition_unfolding,[],[f57,f74])).
% 7.61/1.48  
% 7.61/1.48  fof(f111,plain,(
% 7.61/1.48    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.61/1.48    inference(equality_resolution,[],[f95])).
% 7.61/1.48  
% 7.61/1.48  fof(f73,plain,(
% 7.61/1.48    sK2 != sK4),
% 7.61/1.48    inference(cnf_transformation,[],[f39])).
% 7.61/1.48  
% 7.61/1.48  fof(f72,plain,(
% 7.61/1.48    sK2 != sK3),
% 7.61/1.48    inference(cnf_transformation,[],[f39])).
% 7.61/1.48  
% 7.61/1.48  cnf(c_14,plain,
% 7.61/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 7.61/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1855,plain,
% 7.61/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
% 7.61/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22,plain,
% 7.61/1.48      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X0,X1) ),
% 7.61/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3463,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X1,X2,X0,X3) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_22,c_1]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11316,plain,
% 7.61/1.48      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X0,X1,X3) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_1,c_3463]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11388,plain,
% 7.61/1.48      ( k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_11316,c_22]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_5,plain,
% 7.61/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_28,negated_conjecture,
% 7.61/1.48      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.61/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_216,plain,
% 7.61/1.48      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 7.61/1.48      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 7.61/1.48      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_217,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_216]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2665,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_22,c_217]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_0,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.61/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2760,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2665,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2599,plain,
% 7.61/1.48      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2761,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_2760,c_2599]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3459,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK4,sK3,sK3,sK2) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2761,c_1]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11599,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK4,sK4,sK2,sK3) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_11388,c_3459]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3,plain,
% 7.61/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.61/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_7,plain,
% 7.61/1.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.61/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_209,plain,
% 7.61/1.48      ( X0 != X1
% 7.61/1.48      | k4_xboole_0(X2,X0) != X3
% 7.61/1.48      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_210,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_209]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4039,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_210,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4041,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_4039,c_6]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.61/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2662,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6353,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4041,c_2662]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4659,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4041,c_2]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4042,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_4041,c_210]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4660,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_4659,c_4042]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6380,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_6353,c_4660]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2663,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4793,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4041,c_2663]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4799,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_4793,c_6,c_4042]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4803,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2,c_4799]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6068,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4799,c_4803]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6119,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0))) = X0 ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_6068,c_4799]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6120,plain,
% 7.61/1.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_6119,c_4041,c_4042]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_6381,plain,
% 7.61/1.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_6380,c_2599,c_4042,c_6120]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11600,plain,
% 7.61/1.48      ( k2_enumset1(sK4,sK4,sK2,sK3) = k2_enumset1(sK4,sK4,sK3,sK3) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_11599,c_6,c_6381]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_15,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 7.61/1.48      | X0 = X1
% 7.61/1.48      | X0 = X2
% 7.61/1.48      | X0 = X3 ),
% 7.61/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1854,plain,
% 7.61/1.48      ( X0 = X1
% 7.61/1.48      | X0 = X2
% 7.61/1.48      | X0 = X3
% 7.61/1.48      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11810,plain,
% 7.61/1.48      ( sK3 = X0
% 7.61/1.48      | sK4 = X0
% 7.61/1.48      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK2,sK3)) != iProver_top ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_11600,c_1854]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4655,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK4,sK4,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2761,c_4041]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4664,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK4,sK4,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_4655,c_2761]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_5329,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4664,c_2]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2600,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_217,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2605,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_2599,c_2600]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2848,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK4,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_22,c_2605]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4033,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK4,sK3))) = k1_xboole_0 ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2848,c_210]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4656,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK4,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK4,sK3)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2848,c_4041]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4663,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK4,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_4656,c_2848]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4670,plain,
% 7.61/1.48      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_4033,c_4663]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4806,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK4,sK4,sK3,sK3) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_2761,c_4799]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_5330,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k2_enumset1(sK4,sK4,sK3,sK3)) = k1_xboole_0 ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_5329,c_4670,c_4806]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11796,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK2,sK3),k2_enumset1(sK4,sK4,sK2,sK3)) = k1_xboole_0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_11600,c_5330]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2601,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2604,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_2601,c_4]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_12305,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK2,sK3),k1_xboole_0) = k2_enumset1(sK4,sK4,sK2,sK3) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_11796,c_2604]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11799,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK2,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_11600,c_2761]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11800,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK2,sK3)) = k1_xboole_0 ),
% 7.61/1.48      inference(demodulation,[status(thm)],[c_11799,c_6381]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11836,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK2,sK3),k1_xboole_0) = k2_enumset1(sK2,sK3,sK4,sK2) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_11800,c_3463]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_12306,plain,
% 7.61/1.48      ( k2_enumset1(sK2,sK3,sK4,sK2) = k2_enumset1(sK4,sK4,sK2,sK3) ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_12305,c_11836]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_25739,plain,
% 7.61/1.48      ( sK3 = X0
% 7.61/1.48      | sK4 = X0
% 7.61/1.48      | r2_hidden(X0,k2_enumset1(sK2,sK3,sK4,sK2)) != iProver_top ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_11810,c_12306]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_23,plain,
% 7.61/1.48      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
% 7.61/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3465,plain,
% 7.61/1.48      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X2,X1,X0,X3) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_23,c_1]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_18217,plain,
% 7.61/1.48      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_3465,c_1]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2758,plain,
% 7.61/1.48      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X0,X2) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_23,c_22]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_11823,plain,
% 7.61/1.48      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK4,sK3)) = k1_xboole_0 ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_2758,c_11800]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12317,plain,
% 7.61/1.49      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK4,sK3),k1_xboole_0) = k2_enumset1(sK4,sK3,sK2,sK2) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_11823,c_3463]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12336,plain,
% 7.61/1.49      ( k2_enumset1(sK4,sK3,sK2,sK2) = k2_enumset1(sK2,sK2,sK4,sK3) ),
% 7.61/1.49      inference(demodulation,[status(thm)],[c_12317,c_6]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_18350,plain,
% 7.61/1.49      ( k2_enumset1(sK2,sK3,sK4,sK2) = k2_enumset1(sK2,sK2,sK4,sK3) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_18217,c_12336]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_25740,plain,
% 7.61/1.49      ( sK3 = X0
% 7.61/1.49      | sK4 = X0
% 7.61/1.49      | r2_hidden(X0,k2_enumset1(sK2,sK2,sK4,sK3)) != iProver_top ),
% 7.61/1.49      inference(demodulation,[status(thm)],[c_25739,c_18350]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_25747,plain,
% 7.61/1.49      ( sK3 = sK2 | sK4 = sK2 ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1855,c_25740]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1644,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1890,plain,
% 7.61/1.49      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_1644]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1891,plain,
% 7.61/1.49      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_1890]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1882,plain,
% 7.61/1.49      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_1644]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1883,plain,
% 7.61/1.49      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_1882]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_20,plain,
% 7.61/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_36,plain,
% 7.61/1.49      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_21,plain,
% 7.61/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.61/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_33,plain,
% 7.61/1.49      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_26,negated_conjecture,
% 7.61/1.49      ( sK2 != sK4 ),
% 7.61/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_27,negated_conjecture,
% 7.61/1.49      ( sK2 != sK3 ),
% 7.61/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(contradiction,plain,
% 7.61/1.49      ( $false ),
% 7.61/1.49      inference(minisat,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_25747,c_1891,c_1883,c_36,c_33,c_26,c_27]) ).
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  ------                               Statistics
% 7.61/1.49  
% 7.61/1.49  ------ General
% 7.61/1.49  
% 7.61/1.49  abstr_ref_over_cycles:                  0
% 7.61/1.49  abstr_ref_under_cycles:                 0
% 7.61/1.49  gc_basic_clause_elim:                   0
% 7.61/1.49  forced_gc_time:                         0
% 7.61/1.49  parsing_time:                           0.009
% 7.61/1.49  unif_index_cands_time:                  0.
% 7.61/1.49  unif_index_add_time:                    0.
% 7.61/1.49  orderings_time:                         0.
% 7.61/1.49  out_proof_time:                         0.008
% 7.61/1.49  total_time:                             0.798
% 7.61/1.49  num_of_symbols:                         44
% 7.61/1.49  num_of_terms:                           27298
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing
% 7.61/1.49  
% 7.61/1.49  num_of_splits:                          0
% 7.61/1.49  num_of_split_atoms:                     0
% 7.61/1.49  num_of_reused_defs:                     0
% 7.61/1.49  num_eq_ax_congr_red:                    37
% 7.61/1.49  num_of_sem_filtered_clauses:            1
% 7.61/1.49  num_of_subtypes:                        0
% 7.61/1.49  monotx_restored_types:                  0
% 7.61/1.49  sat_num_of_epr_types:                   0
% 7.61/1.49  sat_num_of_non_cyclic_types:            0
% 7.61/1.49  sat_guarded_non_collapsed_types:        0
% 7.61/1.49  num_pure_diseq_elim:                    0
% 7.61/1.49  simp_replaced_by:                       0
% 7.61/1.49  res_preprocessed:                       123
% 7.61/1.49  prep_upred:                             0
% 7.61/1.49  prep_unflattend:                        100
% 7.61/1.49  smt_new_axioms:                         0
% 7.61/1.49  pred_elim_cands:                        1
% 7.61/1.49  pred_elim:                              2
% 7.61/1.49  pred_elim_cl:                           2
% 7.61/1.49  pred_elim_cycles:                       4
% 7.61/1.49  merged_defs:                            0
% 7.61/1.49  merged_defs_ncl:                        0
% 7.61/1.49  bin_hyper_res:                          0
% 7.61/1.49  prep_cycles:                            4
% 7.61/1.49  pred_elim_time:                         0.022
% 7.61/1.49  splitting_time:                         0.
% 7.61/1.49  sem_filter_time:                        0.
% 7.61/1.49  monotx_time:                            0.
% 7.61/1.49  subtype_inf_time:                       0.
% 7.61/1.49  
% 7.61/1.49  ------ Problem properties
% 7.61/1.49  
% 7.61/1.49  clauses:                                27
% 7.61/1.49  conjectures:                            2
% 7.61/1.49  epr:                                    2
% 7.61/1.49  horn:                                   23
% 7.61/1.49  ground:                                 3
% 7.61/1.49  unary:                                  18
% 7.61/1.49  binary:                                 0
% 7.61/1.49  lits:                                   49
% 7.61/1.49  lits_eq:                                35
% 7.61/1.49  fd_pure:                                0
% 7.61/1.49  fd_pseudo:                              0
% 7.61/1.49  fd_cond:                                0
% 7.61/1.49  fd_pseudo_cond:                         7
% 7.61/1.49  ac_symbols:                             0
% 7.61/1.49  
% 7.61/1.49  ------ Propositional Solver
% 7.61/1.49  
% 7.61/1.49  prop_solver_calls:                      32
% 7.61/1.49  prop_fast_solver_calls:                 1058
% 7.61/1.49  smt_solver_calls:                       0
% 7.61/1.49  smt_fast_solver_calls:                  0
% 7.61/1.49  prop_num_of_clauses:                    7221
% 7.61/1.49  prop_preprocess_simplified:             16766
% 7.61/1.49  prop_fo_subsumed:                       0
% 7.61/1.49  prop_solver_time:                       0.
% 7.61/1.49  smt_solver_time:                        0.
% 7.61/1.49  smt_fast_solver_time:                   0.
% 7.61/1.49  prop_fast_solver_time:                  0.
% 7.61/1.49  prop_unsat_core_time:                   0.
% 7.61/1.49  
% 7.61/1.49  ------ QBF
% 7.61/1.49  
% 7.61/1.49  qbf_q_res:                              0
% 7.61/1.49  qbf_num_tautologies:                    0
% 7.61/1.49  qbf_prep_cycles:                        0
% 7.61/1.49  
% 7.61/1.49  ------ BMC1
% 7.61/1.49  
% 7.61/1.49  bmc1_current_bound:                     -1
% 7.61/1.49  bmc1_last_solved_bound:                 -1
% 7.61/1.49  bmc1_unsat_core_size:                   -1
% 7.61/1.49  bmc1_unsat_core_parents_size:           -1
% 7.61/1.49  bmc1_merge_next_fun:                    0
% 7.61/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.61/1.49  
% 7.61/1.49  ------ Instantiation
% 7.61/1.49  
% 7.61/1.49  inst_num_of_clauses:                    2264
% 7.61/1.49  inst_num_in_passive:                    918
% 7.61/1.49  inst_num_in_active:                     612
% 7.61/1.49  inst_num_in_unprocessed:                738
% 7.61/1.49  inst_num_of_loops:                      750
% 7.61/1.49  inst_num_of_learning_restarts:          0
% 7.61/1.49  inst_num_moves_active_passive:          136
% 7.61/1.49  inst_lit_activity:                      0
% 7.61/1.49  inst_lit_activity_moves:                0
% 7.61/1.49  inst_num_tautologies:                   0
% 7.61/1.49  inst_num_prop_implied:                  0
% 7.61/1.49  inst_num_existing_simplified:           0
% 7.61/1.49  inst_num_eq_res_simplified:             0
% 7.61/1.49  inst_num_child_elim:                    0
% 7.61/1.49  inst_num_of_dismatching_blockings:      3148
% 7.61/1.49  inst_num_of_non_proper_insts:           3008
% 7.61/1.49  inst_num_of_duplicates:                 0
% 7.61/1.49  inst_inst_num_from_inst_to_res:         0
% 7.61/1.49  inst_dismatching_checking_time:         0.
% 7.61/1.49  
% 7.61/1.49  ------ Resolution
% 7.61/1.49  
% 7.61/1.49  res_num_of_clauses:                     0
% 7.61/1.49  res_num_in_passive:                     0
% 7.61/1.49  res_num_in_active:                      0
% 7.61/1.49  res_num_of_loops:                       127
% 7.61/1.49  res_forward_subset_subsumed:            974
% 7.61/1.49  res_backward_subset_subsumed:           10
% 7.61/1.49  res_forward_subsumed:                   16
% 7.61/1.49  res_backward_subsumed:                  0
% 7.61/1.49  res_forward_subsumption_resolution:     0
% 7.61/1.49  res_backward_subsumption_resolution:    0
% 7.61/1.49  res_clause_to_clause_subsumption:       35752
% 7.61/1.49  res_orphan_elimination:                 0
% 7.61/1.49  res_tautology_del:                      83
% 7.61/1.49  res_num_eq_res_simplified:              0
% 7.61/1.49  res_num_sel_changes:                    0
% 7.61/1.49  res_moves_from_active_to_pass:          0
% 7.61/1.49  
% 7.61/1.49  ------ Superposition
% 7.61/1.49  
% 7.61/1.49  sup_time_total:                         0.
% 7.61/1.49  sup_time_generating:                    0.
% 7.61/1.49  sup_time_sim_full:                      0.
% 7.61/1.49  sup_time_sim_immed:                     0.
% 7.61/1.49  
% 7.61/1.49  sup_num_of_clauses:                     875
% 7.61/1.49  sup_num_in_active:                      101
% 7.61/1.49  sup_num_in_passive:                     774
% 7.61/1.49  sup_num_of_loops:                       148
% 7.61/1.49  sup_fw_superposition:                   2671
% 7.61/1.49  sup_bw_superposition:                   2259
% 7.61/1.49  sup_immediate_simplified:               1800
% 7.61/1.49  sup_given_eliminated:                   6
% 7.61/1.49  comparisons_done:                       0
% 7.61/1.49  comparisons_avoided:                    23
% 7.61/1.49  
% 7.61/1.49  ------ Simplifications
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  sim_fw_subset_subsumed:                 12
% 7.61/1.49  sim_bw_subset_subsumed:                 0
% 7.61/1.49  sim_fw_subsumed:                        256
% 7.61/1.49  sim_bw_subsumed:                        15
% 7.61/1.49  sim_fw_subsumption_res:                 0
% 7.61/1.49  sim_bw_subsumption_res:                 0
% 7.61/1.49  sim_tautology_del:                      0
% 7.61/1.49  sim_eq_tautology_del:                   718
% 7.61/1.49  sim_eq_res_simp:                        0
% 7.61/1.49  sim_fw_demodulated:                     915
% 7.61/1.49  sim_bw_demodulated:                     84
% 7.61/1.49  sim_light_normalised:                   1061
% 7.61/1.49  sim_joinable_taut:                      0
% 7.61/1.49  sim_joinable_simp:                      0
% 7.61/1.49  sim_ac_normalised:                      0
% 7.61/1.49  sim_smt_subsumption:                    0
% 7.61/1.49  
%------------------------------------------------------------------------------
