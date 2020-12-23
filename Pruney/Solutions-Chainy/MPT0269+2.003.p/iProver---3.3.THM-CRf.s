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
% DateTime   : Thu Dec  3 11:35:45 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 588 expanded)
%              Number of clauses        :   54 ( 118 expanded)
%              Number of leaves         :   22 ( 169 expanded)
%              Depth                    :   19
%              Number of atoms          :  360 (1204 expanded)
%              Number of equality atoms :  186 ( 857 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f77,f85])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f81,f66,f86])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 )
   => ( k1_tarski(sK4) != sK3
      & k1_xboole_0 != sK3
      & k4_xboole_0(sK3,k1_tarski(sK4)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_tarski(sK4) != sK3
    & k1_xboole_0 != sK3
    & k4_xboole_0(sK3,k1_tarski(sK4)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f44])).

fof(f82,plain,(
    k4_xboole_0(sK3,k1_tarski(sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

fof(f108,plain,(
    k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f82,f66,f86])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f56,f66,f66])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f116,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f72,f66,f66])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f84,plain,(
    k1_tarski(sK4) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    k2_enumset1(sK4,sK4,sK4,sK4) != sK3 ),
    inference(definition_unfolding,[],[f84,f86])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f70,f66])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f74,f86])).

fof(f114,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f103])).

fof(f115,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f114])).

fof(f83,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1096,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1117,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_34,negated_conjecture,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_0,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2329,plain,
    ( k2_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3))) = k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_34,c_0])).

cnf(c_21,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1547,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_21,c_2])).

cnf(c_2348,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_2329,c_1547])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1110,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12197,plain,
    ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2348,c_1110])).

cnf(c_12461,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_12197])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1097,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12593,plain,
    ( sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = sK4
    | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12461,c_1097])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2683,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_2348,c_1])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1101,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6267,plain,
    ( k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2683,c_1101])).

cnf(c_12862,plain,
    ( sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = sK4
    | k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12593,c_6267])).

cnf(c_32,negated_conjecture,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != sK3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1146,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k2_enumset1(sK4,sK4,sK4,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1147,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = sK3
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
    | r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1307,plain,
    ( r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1314,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != k1_xboole_0
    | r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_1102,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7213,plain,
    ( k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != k1_xboole_0
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2348,c_1102])).

cnf(c_16116,plain,
    ( sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12862,c_34,c_32,c_1147,c_1314,c_7213])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13169,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2348,c_1111])).

cnf(c_14427,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0),sK3) != iProver_top
    | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_13169])).

cnf(c_16122,plain,
    ( r2_hidden(sK4,sK3) != iProver_top
    | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16116,c_14427])).

cnf(c_16128,plain,
    ( r2_hidden(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16122,c_34,c_32,c_1147,c_1314,c_6267,c_7213])).

cnf(c_16132,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3 ),
    inference(superposition,[status(thm)],[c_1096,c_16128])).

cnf(c_2211,plain,
    ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_34,c_1])).

cnf(c_24,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2214,plain,
    ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2211,c_24])).

cnf(c_2404,plain,
    ( k5_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2214,c_34])).

cnf(c_16133,plain,
    ( sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16132,c_2214,c_2404])).

cnf(c_572,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1172,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1173,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_28,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_45,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_42,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16133,c_1173,c_45,c_42,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.16/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.01  
% 4.16/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.16/1.01  
% 4.16/1.01  ------  iProver source info
% 4.16/1.01  
% 4.16/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.16/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.16/1.01  git: non_committed_changes: false
% 4.16/1.01  git: last_make_outside_of_git: false
% 4.16/1.01  
% 4.16/1.01  ------ 
% 4.16/1.01  
% 4.16/1.01  ------ Input Options
% 4.16/1.01  
% 4.16/1.01  --out_options                           all
% 4.16/1.01  --tptp_safe_out                         true
% 4.16/1.01  --problem_path                          ""
% 4.16/1.01  --include_path                          ""
% 4.16/1.01  --clausifier                            res/vclausify_rel
% 4.16/1.01  --clausifier_options                    ""
% 4.16/1.01  --stdin                                 false
% 4.16/1.01  --stats_out                             all
% 4.16/1.01  
% 4.16/1.01  ------ General Options
% 4.16/1.01  
% 4.16/1.01  --fof                                   false
% 4.16/1.01  --time_out_real                         305.
% 4.16/1.01  --time_out_virtual                      -1.
% 4.16/1.01  --symbol_type_check                     false
% 4.16/1.01  --clausify_out                          false
% 4.16/1.01  --sig_cnt_out                           false
% 4.16/1.01  --trig_cnt_out                          false
% 4.16/1.01  --trig_cnt_out_tolerance                1.
% 4.16/1.01  --trig_cnt_out_sk_spl                   false
% 4.16/1.01  --abstr_cl_out                          false
% 4.16/1.01  
% 4.16/1.01  ------ Global Options
% 4.16/1.01  
% 4.16/1.01  --schedule                              default
% 4.16/1.01  --add_important_lit                     false
% 4.16/1.01  --prop_solver_per_cl                    1000
% 4.16/1.01  --min_unsat_core                        false
% 4.16/1.01  --soft_assumptions                      false
% 4.16/1.01  --soft_lemma_size                       3
% 4.16/1.01  --prop_impl_unit_size                   0
% 4.16/1.01  --prop_impl_unit                        []
% 4.16/1.01  --share_sel_clauses                     true
% 4.16/1.01  --reset_solvers                         false
% 4.16/1.01  --bc_imp_inh                            [conj_cone]
% 4.16/1.01  --conj_cone_tolerance                   3.
% 4.16/1.01  --extra_neg_conj                        none
% 4.16/1.01  --large_theory_mode                     true
% 4.16/1.01  --prolific_symb_bound                   200
% 4.16/1.01  --lt_threshold                          2000
% 4.16/1.01  --clause_weak_htbl                      true
% 4.16/1.01  --gc_record_bc_elim                     false
% 4.16/1.01  
% 4.16/1.01  ------ Preprocessing Options
% 4.16/1.01  
% 4.16/1.01  --preprocessing_flag                    true
% 4.16/1.01  --time_out_prep_mult                    0.1
% 4.16/1.01  --splitting_mode                        input
% 4.16/1.01  --splitting_grd                         true
% 4.16/1.01  --splitting_cvd                         false
% 4.16/1.01  --splitting_cvd_svl                     false
% 4.16/1.01  --splitting_nvd                         32
% 4.16/1.01  --sub_typing                            true
% 4.16/1.01  --prep_gs_sim                           true
% 4.16/1.01  --prep_unflatten                        true
% 4.16/1.01  --prep_res_sim                          true
% 4.16/1.01  --prep_upred                            true
% 4.16/1.01  --prep_sem_filter                       exhaustive
% 4.16/1.01  --prep_sem_filter_out                   false
% 4.16/1.01  --pred_elim                             true
% 4.16/1.01  --res_sim_input                         true
% 4.16/1.01  --eq_ax_congr_red                       true
% 4.16/1.01  --pure_diseq_elim                       true
% 4.16/1.01  --brand_transform                       false
% 4.16/1.01  --non_eq_to_eq                          false
% 4.16/1.01  --prep_def_merge                        true
% 4.16/1.01  --prep_def_merge_prop_impl              false
% 4.16/1.01  --prep_def_merge_mbd                    true
% 4.16/1.01  --prep_def_merge_tr_red                 false
% 4.16/1.01  --prep_def_merge_tr_cl                  false
% 4.16/1.01  --smt_preprocessing                     true
% 4.16/1.01  --smt_ac_axioms                         fast
% 4.16/1.01  --preprocessed_out                      false
% 4.16/1.01  --preprocessed_stats                    false
% 4.16/1.01  
% 4.16/1.01  ------ Abstraction refinement Options
% 4.16/1.01  
% 4.16/1.01  --abstr_ref                             []
% 4.16/1.01  --abstr_ref_prep                        false
% 4.16/1.01  --abstr_ref_until_sat                   false
% 4.16/1.01  --abstr_ref_sig_restrict                funpre
% 4.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.16/1.01  --abstr_ref_under                       []
% 4.16/1.01  
% 4.16/1.01  ------ SAT Options
% 4.16/1.01  
% 4.16/1.01  --sat_mode                              false
% 4.16/1.01  --sat_fm_restart_options                ""
% 4.16/1.01  --sat_gr_def                            false
% 4.16/1.01  --sat_epr_types                         true
% 4.16/1.01  --sat_non_cyclic_types                  false
% 4.16/1.01  --sat_finite_models                     false
% 4.16/1.01  --sat_fm_lemmas                         false
% 4.16/1.01  --sat_fm_prep                           false
% 4.16/1.01  --sat_fm_uc_incr                        true
% 4.16/1.01  --sat_out_model                         small
% 4.16/1.01  --sat_out_clauses                       false
% 4.16/1.01  
% 4.16/1.01  ------ QBF Options
% 4.16/1.01  
% 4.16/1.01  --qbf_mode                              false
% 4.16/1.01  --qbf_elim_univ                         false
% 4.16/1.01  --qbf_dom_inst                          none
% 4.16/1.01  --qbf_dom_pre_inst                      false
% 4.16/1.01  --qbf_sk_in                             false
% 4.16/1.01  --qbf_pred_elim                         true
% 4.16/1.01  --qbf_split                             512
% 4.16/1.01  
% 4.16/1.01  ------ BMC1 Options
% 4.16/1.01  
% 4.16/1.01  --bmc1_incremental                      false
% 4.16/1.01  --bmc1_axioms                           reachable_all
% 4.16/1.01  --bmc1_min_bound                        0
% 4.16/1.01  --bmc1_max_bound                        -1
% 4.16/1.01  --bmc1_max_bound_default                -1
% 4.16/1.01  --bmc1_symbol_reachability              true
% 4.16/1.01  --bmc1_property_lemmas                  false
% 4.16/1.01  --bmc1_k_induction                      false
% 4.16/1.01  --bmc1_non_equiv_states                 false
% 4.16/1.01  --bmc1_deadlock                         false
% 4.16/1.01  --bmc1_ucm                              false
% 4.16/1.01  --bmc1_add_unsat_core                   none
% 4.16/1.01  --bmc1_unsat_core_children              false
% 4.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.16/1.01  --bmc1_out_stat                         full
% 4.16/1.01  --bmc1_ground_init                      false
% 4.16/1.01  --bmc1_pre_inst_next_state              false
% 4.16/1.01  --bmc1_pre_inst_state                   false
% 4.16/1.01  --bmc1_pre_inst_reach_state             false
% 4.16/1.01  --bmc1_out_unsat_core                   false
% 4.16/1.01  --bmc1_aig_witness_out                  false
% 4.16/1.01  --bmc1_verbose                          false
% 4.16/1.01  --bmc1_dump_clauses_tptp                false
% 4.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.16/1.01  --bmc1_dump_file                        -
% 4.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.16/1.01  --bmc1_ucm_extend_mode                  1
% 4.16/1.01  --bmc1_ucm_init_mode                    2
% 4.16/1.01  --bmc1_ucm_cone_mode                    none
% 4.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.16/1.01  --bmc1_ucm_relax_model                  4
% 4.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.16/1.01  --bmc1_ucm_layered_model                none
% 4.16/1.01  --bmc1_ucm_max_lemma_size               10
% 4.16/1.01  
% 4.16/1.01  ------ AIG Options
% 4.16/1.01  
% 4.16/1.01  --aig_mode                              false
% 4.16/1.01  
% 4.16/1.01  ------ Instantiation Options
% 4.16/1.01  
% 4.16/1.01  --instantiation_flag                    true
% 4.16/1.01  --inst_sos_flag                         true
% 4.16/1.01  --inst_sos_phase                        true
% 4.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.16/1.01  --inst_lit_sel_side                     num_symb
% 4.16/1.01  --inst_solver_per_active                1400
% 4.16/1.01  --inst_solver_calls_frac                1.
% 4.16/1.01  --inst_passive_queue_type               priority_queues
% 4.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.16/1.01  --inst_passive_queues_freq              [25;2]
% 4.16/1.01  --inst_dismatching                      true
% 4.16/1.01  --inst_eager_unprocessed_to_passive     true
% 4.16/1.01  --inst_prop_sim_given                   true
% 4.16/1.01  --inst_prop_sim_new                     false
% 4.16/1.01  --inst_subs_new                         false
% 4.16/1.01  --inst_eq_res_simp                      false
% 4.16/1.01  --inst_subs_given                       false
% 4.16/1.01  --inst_orphan_elimination               true
% 4.16/1.01  --inst_learning_loop_flag               true
% 4.16/1.01  --inst_learning_start                   3000
% 4.16/1.01  --inst_learning_factor                  2
% 4.16/1.01  --inst_start_prop_sim_after_learn       3
% 4.16/1.01  --inst_sel_renew                        solver
% 4.16/1.01  --inst_lit_activity_flag                true
% 4.16/1.01  --inst_restr_to_given                   false
% 4.16/1.01  --inst_activity_threshold               500
% 4.16/1.01  --inst_out_proof                        true
% 4.16/1.01  
% 4.16/1.01  ------ Resolution Options
% 4.16/1.01  
% 4.16/1.01  --resolution_flag                       true
% 4.16/1.01  --res_lit_sel                           adaptive
% 4.16/1.01  --res_lit_sel_side                      none
% 4.16/1.01  --res_ordering                          kbo
% 4.16/1.01  --res_to_prop_solver                    active
% 4.16/1.01  --res_prop_simpl_new                    false
% 4.16/1.01  --res_prop_simpl_given                  true
% 4.16/1.01  --res_passive_queue_type                priority_queues
% 4.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.16/1.01  --res_passive_queues_freq               [15;5]
% 4.16/1.01  --res_forward_subs                      full
% 4.16/1.01  --res_backward_subs                     full
% 4.16/1.01  --res_forward_subs_resolution           true
% 4.16/1.01  --res_backward_subs_resolution          true
% 4.16/1.01  --res_orphan_elimination                true
% 4.16/1.01  --res_time_limit                        2.
% 4.16/1.01  --res_out_proof                         true
% 4.16/1.01  
% 4.16/1.01  ------ Superposition Options
% 4.16/1.01  
% 4.16/1.01  --superposition_flag                    true
% 4.16/1.01  --sup_passive_queue_type                priority_queues
% 4.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.16/1.01  --demod_completeness_check              fast
% 4.16/1.01  --demod_use_ground                      true
% 4.16/1.01  --sup_to_prop_solver                    passive
% 4.16/1.01  --sup_prop_simpl_new                    true
% 4.16/1.01  --sup_prop_simpl_given                  true
% 4.16/1.01  --sup_fun_splitting                     true
% 4.16/1.01  --sup_smt_interval                      50000
% 4.16/1.01  
% 4.16/1.01  ------ Superposition Simplification Setup
% 4.16/1.01  
% 4.16/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.16/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.16/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.16/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.16/1.01  --sup_immed_triv                        [TrivRules]
% 4.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/1.01  --sup_immed_bw_main                     []
% 4.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/1.01  --sup_input_bw                          []
% 4.16/1.01  
% 4.16/1.01  ------ Combination Options
% 4.16/1.01  
% 4.16/1.01  --comb_res_mult                         3
% 4.16/1.01  --comb_sup_mult                         2
% 4.16/1.01  --comb_inst_mult                        10
% 4.16/1.01  
% 4.16/1.01  ------ Debug Options
% 4.16/1.01  
% 4.16/1.01  --dbg_backtrace                         false
% 4.16/1.01  --dbg_dump_prop_clauses                 false
% 4.16/1.01  --dbg_dump_prop_clauses_file            -
% 4.16/1.01  --dbg_out_stat                          false
% 4.16/1.01  ------ Parsing...
% 4.16/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.16/1.01  
% 4.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.16/1.01  
% 4.16/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.16/1.01  
% 4.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.01  ------ Proving...
% 4.16/1.01  ------ Problem Properties 
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  clauses                                 34
% 4.16/1.01  conjectures                             3
% 4.16/1.01  EPR                                     4
% 4.16/1.01  Horn                                    24
% 4.16/1.01  unary                                   12
% 4.16/1.01  binary                                  10
% 4.16/1.01  lits                                    69
% 4.16/1.01  lits eq                                 24
% 4.16/1.01  fd_pure                                 0
% 4.16/1.01  fd_pseudo                               0
% 4.16/1.01  fd_cond                                 1
% 4.16/1.01  fd_pseudo_cond                          6
% 4.16/1.01  AC symbols                              0
% 4.16/1.01  
% 4.16/1.01  ------ Schedule dynamic 5 is on 
% 4.16/1.01  
% 4.16/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  ------ 
% 4.16/1.01  Current options:
% 4.16/1.01  ------ 
% 4.16/1.01  
% 4.16/1.01  ------ Input Options
% 4.16/1.01  
% 4.16/1.01  --out_options                           all
% 4.16/1.01  --tptp_safe_out                         true
% 4.16/1.01  --problem_path                          ""
% 4.16/1.01  --include_path                          ""
% 4.16/1.01  --clausifier                            res/vclausify_rel
% 4.16/1.01  --clausifier_options                    ""
% 4.16/1.01  --stdin                                 false
% 4.16/1.01  --stats_out                             all
% 4.16/1.01  
% 4.16/1.01  ------ General Options
% 4.16/1.01  
% 4.16/1.01  --fof                                   false
% 4.16/1.01  --time_out_real                         305.
% 4.16/1.01  --time_out_virtual                      -1.
% 4.16/1.01  --symbol_type_check                     false
% 4.16/1.01  --clausify_out                          false
% 4.16/1.01  --sig_cnt_out                           false
% 4.16/1.01  --trig_cnt_out                          false
% 4.16/1.01  --trig_cnt_out_tolerance                1.
% 4.16/1.01  --trig_cnt_out_sk_spl                   false
% 4.16/1.01  --abstr_cl_out                          false
% 4.16/1.01  
% 4.16/1.01  ------ Global Options
% 4.16/1.01  
% 4.16/1.01  --schedule                              default
% 4.16/1.01  --add_important_lit                     false
% 4.16/1.01  --prop_solver_per_cl                    1000
% 4.16/1.01  --min_unsat_core                        false
% 4.16/1.01  --soft_assumptions                      false
% 4.16/1.01  --soft_lemma_size                       3
% 4.16/1.01  --prop_impl_unit_size                   0
% 4.16/1.01  --prop_impl_unit                        []
% 4.16/1.01  --share_sel_clauses                     true
% 4.16/1.01  --reset_solvers                         false
% 4.16/1.01  --bc_imp_inh                            [conj_cone]
% 4.16/1.01  --conj_cone_tolerance                   3.
% 4.16/1.01  --extra_neg_conj                        none
% 4.16/1.01  --large_theory_mode                     true
% 4.16/1.01  --prolific_symb_bound                   200
% 4.16/1.01  --lt_threshold                          2000
% 4.16/1.01  --clause_weak_htbl                      true
% 4.16/1.01  --gc_record_bc_elim                     false
% 4.16/1.01  
% 4.16/1.01  ------ Preprocessing Options
% 4.16/1.01  
% 4.16/1.01  --preprocessing_flag                    true
% 4.16/1.01  --time_out_prep_mult                    0.1
% 4.16/1.01  --splitting_mode                        input
% 4.16/1.01  --splitting_grd                         true
% 4.16/1.01  --splitting_cvd                         false
% 4.16/1.01  --splitting_cvd_svl                     false
% 4.16/1.01  --splitting_nvd                         32
% 4.16/1.01  --sub_typing                            true
% 4.16/1.01  --prep_gs_sim                           true
% 4.16/1.01  --prep_unflatten                        true
% 4.16/1.01  --prep_res_sim                          true
% 4.16/1.01  --prep_upred                            true
% 4.16/1.01  --prep_sem_filter                       exhaustive
% 4.16/1.01  --prep_sem_filter_out                   false
% 4.16/1.01  --pred_elim                             true
% 4.16/1.01  --res_sim_input                         true
% 4.16/1.01  --eq_ax_congr_red                       true
% 4.16/1.01  --pure_diseq_elim                       true
% 4.16/1.01  --brand_transform                       false
% 4.16/1.01  --non_eq_to_eq                          false
% 4.16/1.01  --prep_def_merge                        true
% 4.16/1.01  --prep_def_merge_prop_impl              false
% 4.16/1.01  --prep_def_merge_mbd                    true
% 4.16/1.01  --prep_def_merge_tr_red                 false
% 4.16/1.01  --prep_def_merge_tr_cl                  false
% 4.16/1.01  --smt_preprocessing                     true
% 4.16/1.01  --smt_ac_axioms                         fast
% 4.16/1.01  --preprocessed_out                      false
% 4.16/1.01  --preprocessed_stats                    false
% 4.16/1.01  
% 4.16/1.01  ------ Abstraction refinement Options
% 4.16/1.01  
% 4.16/1.01  --abstr_ref                             []
% 4.16/1.01  --abstr_ref_prep                        false
% 4.16/1.01  --abstr_ref_until_sat                   false
% 4.16/1.01  --abstr_ref_sig_restrict                funpre
% 4.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.16/1.01  --abstr_ref_under                       []
% 4.16/1.01  
% 4.16/1.01  ------ SAT Options
% 4.16/1.01  
% 4.16/1.01  --sat_mode                              false
% 4.16/1.01  --sat_fm_restart_options                ""
% 4.16/1.01  --sat_gr_def                            false
% 4.16/1.01  --sat_epr_types                         true
% 4.16/1.01  --sat_non_cyclic_types                  false
% 4.16/1.01  --sat_finite_models                     false
% 4.16/1.01  --sat_fm_lemmas                         false
% 4.16/1.01  --sat_fm_prep                           false
% 4.16/1.01  --sat_fm_uc_incr                        true
% 4.16/1.01  --sat_out_model                         small
% 4.16/1.01  --sat_out_clauses                       false
% 4.16/1.01  
% 4.16/1.01  ------ QBF Options
% 4.16/1.01  
% 4.16/1.01  --qbf_mode                              false
% 4.16/1.01  --qbf_elim_univ                         false
% 4.16/1.01  --qbf_dom_inst                          none
% 4.16/1.01  --qbf_dom_pre_inst                      false
% 4.16/1.01  --qbf_sk_in                             false
% 4.16/1.01  --qbf_pred_elim                         true
% 4.16/1.01  --qbf_split                             512
% 4.16/1.01  
% 4.16/1.01  ------ BMC1 Options
% 4.16/1.01  
% 4.16/1.01  --bmc1_incremental                      false
% 4.16/1.01  --bmc1_axioms                           reachable_all
% 4.16/1.01  --bmc1_min_bound                        0
% 4.16/1.01  --bmc1_max_bound                        -1
% 4.16/1.01  --bmc1_max_bound_default                -1
% 4.16/1.01  --bmc1_symbol_reachability              true
% 4.16/1.01  --bmc1_property_lemmas                  false
% 4.16/1.01  --bmc1_k_induction                      false
% 4.16/1.01  --bmc1_non_equiv_states                 false
% 4.16/1.01  --bmc1_deadlock                         false
% 4.16/1.01  --bmc1_ucm                              false
% 4.16/1.01  --bmc1_add_unsat_core                   none
% 4.16/1.01  --bmc1_unsat_core_children              false
% 4.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.16/1.01  --bmc1_out_stat                         full
% 4.16/1.01  --bmc1_ground_init                      false
% 4.16/1.01  --bmc1_pre_inst_next_state              false
% 4.16/1.01  --bmc1_pre_inst_state                   false
% 4.16/1.01  --bmc1_pre_inst_reach_state             false
% 4.16/1.01  --bmc1_out_unsat_core                   false
% 4.16/1.01  --bmc1_aig_witness_out                  false
% 4.16/1.01  --bmc1_verbose                          false
% 4.16/1.01  --bmc1_dump_clauses_tptp                false
% 4.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.16/1.01  --bmc1_dump_file                        -
% 4.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.16/1.01  --bmc1_ucm_extend_mode                  1
% 4.16/1.01  --bmc1_ucm_init_mode                    2
% 4.16/1.01  --bmc1_ucm_cone_mode                    none
% 4.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.16/1.01  --bmc1_ucm_relax_model                  4
% 4.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.16/1.01  --bmc1_ucm_layered_model                none
% 4.16/1.01  --bmc1_ucm_max_lemma_size               10
% 4.16/1.01  
% 4.16/1.01  ------ AIG Options
% 4.16/1.01  
% 4.16/1.01  --aig_mode                              false
% 4.16/1.01  
% 4.16/1.01  ------ Instantiation Options
% 4.16/1.01  
% 4.16/1.01  --instantiation_flag                    true
% 4.16/1.01  --inst_sos_flag                         true
% 4.16/1.01  --inst_sos_phase                        true
% 4.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.16/1.01  --inst_lit_sel_side                     none
% 4.16/1.01  --inst_solver_per_active                1400
% 4.16/1.01  --inst_solver_calls_frac                1.
% 4.16/1.01  --inst_passive_queue_type               priority_queues
% 4.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.16/1.01  --inst_passive_queues_freq              [25;2]
% 4.16/1.01  --inst_dismatching                      true
% 4.16/1.01  --inst_eager_unprocessed_to_passive     true
% 4.16/1.01  --inst_prop_sim_given                   true
% 4.16/1.01  --inst_prop_sim_new                     false
% 4.16/1.01  --inst_subs_new                         false
% 4.16/1.01  --inst_eq_res_simp                      false
% 4.16/1.01  --inst_subs_given                       false
% 4.16/1.01  --inst_orphan_elimination               true
% 4.16/1.01  --inst_learning_loop_flag               true
% 4.16/1.01  --inst_learning_start                   3000
% 4.16/1.01  --inst_learning_factor                  2
% 4.16/1.01  --inst_start_prop_sim_after_learn       3
% 4.16/1.01  --inst_sel_renew                        solver
% 4.16/1.01  --inst_lit_activity_flag                true
% 4.16/1.01  --inst_restr_to_given                   false
% 4.16/1.01  --inst_activity_threshold               500
% 4.16/1.01  --inst_out_proof                        true
% 4.16/1.01  
% 4.16/1.01  ------ Resolution Options
% 4.16/1.01  
% 4.16/1.01  --resolution_flag                       false
% 4.16/1.01  --res_lit_sel                           adaptive
% 4.16/1.01  --res_lit_sel_side                      none
% 4.16/1.01  --res_ordering                          kbo
% 4.16/1.01  --res_to_prop_solver                    active
% 4.16/1.01  --res_prop_simpl_new                    false
% 4.16/1.01  --res_prop_simpl_given                  true
% 4.16/1.01  --res_passive_queue_type                priority_queues
% 4.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.16/1.01  --res_passive_queues_freq               [15;5]
% 4.16/1.01  --res_forward_subs                      full
% 4.16/1.01  --res_backward_subs                     full
% 4.16/1.01  --res_forward_subs_resolution           true
% 4.16/1.01  --res_backward_subs_resolution          true
% 4.16/1.01  --res_orphan_elimination                true
% 4.16/1.01  --res_time_limit                        2.
% 4.16/1.01  --res_out_proof                         true
% 4.16/1.01  
% 4.16/1.01  ------ Superposition Options
% 4.16/1.01  
% 4.16/1.01  --superposition_flag                    true
% 4.16/1.01  --sup_passive_queue_type                priority_queues
% 4.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.16/1.01  --demod_completeness_check              fast
% 4.16/1.01  --demod_use_ground                      true
% 4.16/1.01  --sup_to_prop_solver                    passive
% 4.16/1.01  --sup_prop_simpl_new                    true
% 4.16/1.01  --sup_prop_simpl_given                  true
% 4.16/1.01  --sup_fun_splitting                     true
% 4.16/1.01  --sup_smt_interval                      50000
% 4.16/1.01  
% 4.16/1.01  ------ Superposition Simplification Setup
% 4.16/1.01  
% 4.16/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.16/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.16/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.16/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.16/1.01  --sup_immed_triv                        [TrivRules]
% 4.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/1.01  --sup_immed_bw_main                     []
% 4.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/1.01  --sup_input_bw                          []
% 4.16/1.01  
% 4.16/1.01  ------ Combination Options
% 4.16/1.01  
% 4.16/1.01  --comb_res_mult                         3
% 4.16/1.01  --comb_sup_mult                         2
% 4.16/1.01  --comb_inst_mult                        10
% 4.16/1.01  
% 4.16/1.01  ------ Debug Options
% 4.16/1.01  
% 4.16/1.01  --dbg_backtrace                         false
% 4.16/1.01  --dbg_dump_prop_clauses                 false
% 4.16/1.01  --dbg_dump_prop_clauses_file            -
% 4.16/1.01  --dbg_out_stat                          false
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  ------ Proving...
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  % SZS status Theorem for theBenchmark.p
% 4.16/1.01  
% 4.16/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.16/1.01  
% 4.16/1.01  fof(f19,axiom,(
% 4.16/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f43,plain,(
% 4.16/1.01    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 4.16/1.01    inference(nnf_transformation,[],[f19])).
% 4.16/1.01  
% 4.16/1.01  fof(f81,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f43])).
% 4.16/1.01  
% 4.16/1.01  fof(f8,axiom,(
% 4.16/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f66,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.16/1.01    inference(cnf_transformation,[],[f8])).
% 4.16/1.01  
% 4.16/1.01  fof(f16,axiom,(
% 4.16/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f77,plain,(
% 4.16/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f16])).
% 4.16/1.01  
% 4.16/1.01  fof(f17,axiom,(
% 4.16/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f78,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f17])).
% 4.16/1.01  
% 4.16/1.01  fof(f18,axiom,(
% 4.16/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f79,plain,(
% 4.16/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f18])).
% 4.16/1.01  
% 4.16/1.01  fof(f85,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.16/1.01    inference(definition_unfolding,[],[f78,f79])).
% 4.16/1.01  
% 4.16/1.01  fof(f86,plain,(
% 4.16/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.16/1.01    inference(definition_unfolding,[],[f77,f85])).
% 4.16/1.01  
% 4.16/1.01  fof(f105,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 4.16/1.01    inference(definition_unfolding,[],[f81,f66,f86])).
% 4.16/1.01  
% 4.16/1.01  fof(f2,axiom,(
% 4.16/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f22,plain,(
% 4.16/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.16/1.01    inference(ennf_transformation,[],[f2])).
% 4.16/1.01  
% 4.16/1.01  fof(f26,plain,(
% 4.16/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.16/1.01    inference(nnf_transformation,[],[f22])).
% 4.16/1.01  
% 4.16/1.01  fof(f27,plain,(
% 4.16/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.16/1.01    inference(rectify,[],[f26])).
% 4.16/1.01  
% 4.16/1.01  fof(f28,plain,(
% 4.16/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.16/1.01    introduced(choice_axiom,[])).
% 4.16/1.01  
% 4.16/1.01  fof(f29,plain,(
% 4.16/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 4.16/1.01  
% 4.16/1.01  fof(f48,plain,(
% 4.16/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f29])).
% 4.16/1.01  
% 4.16/1.01  fof(f20,conjecture,(
% 4.16/1.01    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f21,negated_conjecture,(
% 4.16/1.01    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 4.16/1.01    inference(negated_conjecture,[],[f20])).
% 4.16/1.01  
% 4.16/1.01  fof(f25,plain,(
% 4.16/1.01    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 4.16/1.01    inference(ennf_transformation,[],[f21])).
% 4.16/1.01  
% 4.16/1.01  fof(f44,plain,(
% 4.16/1.01    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0) => (k1_tarski(sK4) != sK3 & k1_xboole_0 != sK3 & k4_xboole_0(sK3,k1_tarski(sK4)) = k1_xboole_0)),
% 4.16/1.01    introduced(choice_axiom,[])).
% 4.16/1.01  
% 4.16/1.01  fof(f45,plain,(
% 4.16/1.01    k1_tarski(sK4) != sK3 & k1_xboole_0 != sK3 & k4_xboole_0(sK3,k1_tarski(sK4)) = k1_xboole_0),
% 4.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f44])).
% 4.16/1.01  
% 4.16/1.01  fof(f82,plain,(
% 4.16/1.01    k4_xboole_0(sK3,k1_tarski(sK4)) = k1_xboole_0),
% 4.16/1.01    inference(cnf_transformation,[],[f45])).
% 4.16/1.01  
% 4.16/1.01  fof(f108,plain,(
% 4.16/1.01    k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0),
% 4.16/1.01    inference(definition_unfolding,[],[f82,f66,f86])).
% 4.16/1.01  
% 4.16/1.01  fof(f4,axiom,(
% 4.16/1.01    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f56,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f4])).
% 4.16/1.01  
% 4.16/1.01  fof(f87,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,X1)) )),
% 4.16/1.01    inference(definition_unfolding,[],[f56,f66,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f9,axiom,(
% 4.16/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f67,plain,(
% 4.16/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.16/1.01    inference(cnf_transformation,[],[f9])).
% 4.16/1.01  
% 4.16/1.01  fof(f1,axiom,(
% 4.16/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f46,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f1])).
% 4.16/1.01  
% 4.16/1.01  fof(f3,axiom,(
% 4.16/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f30,plain,(
% 4.16/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.16/1.01    inference(nnf_transformation,[],[f3])).
% 4.16/1.01  
% 4.16/1.01  fof(f31,plain,(
% 4.16/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.16/1.01    inference(flattening,[],[f30])).
% 4.16/1.01  
% 4.16/1.01  fof(f32,plain,(
% 4.16/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.16/1.01    inference(rectify,[],[f31])).
% 4.16/1.01  
% 4.16/1.01  fof(f33,plain,(
% 4.16/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.16/1.01    introduced(choice_axiom,[])).
% 4.16/1.01  
% 4.16/1.01  fof(f34,plain,(
% 4.16/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 4.16/1.01  
% 4.16/1.01  fof(f50,plain,(
% 4.16/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.16/1.01    inference(cnf_transformation,[],[f34])).
% 4.16/1.01  
% 4.16/1.01  fof(f94,plain,(
% 4.16/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 4.16/1.01    inference(definition_unfolding,[],[f50,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f111,plain,(
% 4.16/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 4.16/1.01    inference(equality_resolution,[],[f94])).
% 4.16/1.01  
% 4.16/1.01  fof(f15,axiom,(
% 4.16/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f39,plain,(
% 4.16/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.16/1.01    inference(nnf_transformation,[],[f15])).
% 4.16/1.01  
% 4.16/1.01  fof(f40,plain,(
% 4.16/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.16/1.01    inference(rectify,[],[f39])).
% 4.16/1.01  
% 4.16/1.01  fof(f41,plain,(
% 4.16/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 4.16/1.01    introduced(choice_axiom,[])).
% 4.16/1.01  
% 4.16/1.01  fof(f42,plain,(
% 4.16/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 4.16/1.01  
% 4.16/1.01  fof(f73,plain,(
% 4.16/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.16/1.01    inference(cnf_transformation,[],[f42])).
% 4.16/1.01  
% 4.16/1.01  fof(f104,plain,(
% 4.16/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.16/1.01    inference(definition_unfolding,[],[f73,f86])).
% 4.16/1.01  
% 4.16/1.01  fof(f116,plain,(
% 4.16/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 4.16/1.01    inference(equality_resolution,[],[f104])).
% 4.16/1.01  
% 4.16/1.01  fof(f14,axiom,(
% 4.16/1.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f72,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f14])).
% 4.16/1.01  
% 4.16/1.01  fof(f88,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1)) )),
% 4.16/1.01    inference(definition_unfolding,[],[f72,f66,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f10,axiom,(
% 4.16/1.01    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f24,plain,(
% 4.16/1.01    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 4.16/1.01    inference(ennf_transformation,[],[f10])).
% 4.16/1.01  
% 4.16/1.01  fof(f68,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 4.16/1.01    inference(cnf_transformation,[],[f24])).
% 4.16/1.01  
% 4.16/1.01  fof(f97,plain,(
% 4.16/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.16/1.01    inference(definition_unfolding,[],[f68,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f84,plain,(
% 4.16/1.01    k1_tarski(sK4) != sK3),
% 4.16/1.01    inference(cnf_transformation,[],[f45])).
% 4.16/1.01  
% 4.16/1.01  fof(f107,plain,(
% 4.16/1.01    k2_enumset1(sK4,sK4,sK4,sK4) != sK3),
% 4.16/1.01    inference(definition_unfolding,[],[f84,f86])).
% 4.16/1.01  
% 4.16/1.01  fof(f6,axiom,(
% 4.16/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f36,plain,(
% 4.16/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.16/1.01    inference(nnf_transformation,[],[f6])).
% 4.16/1.01  
% 4.16/1.01  fof(f37,plain,(
% 4.16/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.16/1.01    inference(flattening,[],[f36])).
% 4.16/1.01  
% 4.16/1.01  fof(f63,plain,(
% 4.16/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.16/1.01    inference(cnf_transformation,[],[f37])).
% 4.16/1.01  
% 4.16/1.01  fof(f7,axiom,(
% 4.16/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f38,plain,(
% 4.16/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.16/1.01    inference(nnf_transformation,[],[f7])).
% 4.16/1.01  
% 4.16/1.01  fof(f64,plain,(
% 4.16/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.16/1.01    inference(cnf_transformation,[],[f38])).
% 4.16/1.01  
% 4.16/1.01  fof(f96,plain,(
% 4.16/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 4.16/1.01    inference(definition_unfolding,[],[f64,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f51,plain,(
% 4.16/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.16/1.01    inference(cnf_transformation,[],[f34])).
% 4.16/1.01  
% 4.16/1.01  fof(f93,plain,(
% 4.16/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 4.16/1.01    inference(definition_unfolding,[],[f51,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f110,plain,(
% 4.16/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 4.16/1.01    inference(equality_resolution,[],[f93])).
% 4.16/1.01  
% 4.16/1.01  fof(f12,axiom,(
% 4.16/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.01  
% 4.16/1.01  fof(f70,plain,(
% 4.16/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.16/1.01    inference(cnf_transformation,[],[f12])).
% 4.16/1.01  
% 4.16/1.01  fof(f99,plain,(
% 4.16/1.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 4.16/1.01    inference(definition_unfolding,[],[f70,f66])).
% 4.16/1.01  
% 4.16/1.01  fof(f74,plain,(
% 4.16/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.16/1.01    inference(cnf_transformation,[],[f42])).
% 4.16/1.01  
% 4.16/1.01  fof(f103,plain,(
% 4.16/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.16/1.01    inference(definition_unfolding,[],[f74,f86])).
% 4.16/1.01  
% 4.16/1.01  fof(f114,plain,(
% 4.16/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 4.16/1.01    inference(equality_resolution,[],[f103])).
% 4.16/1.01  
% 4.16/1.01  fof(f115,plain,(
% 4.16/1.01    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 4.16/1.01    inference(equality_resolution,[],[f114])).
% 4.16/1.01  
% 4.16/1.01  fof(f83,plain,(
% 4.16/1.01    k1_xboole_0 != sK3),
% 4.16/1.01    inference(cnf_transformation,[],[f45])).
% 4.16/1.01  
% 4.16/1.01  cnf(c_30,plain,
% 4.16/1.01      ( r2_hidden(X0,X1)
% 4.16/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
% 4.16/1.01      inference(cnf_transformation,[],[f105]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1096,plain,
% 4.16/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
% 4.16/1.01      | r2_hidden(X1,X0) = iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_4,plain,
% 4.16/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 4.16/1.01      inference(cnf_transformation,[],[f48]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1117,plain,
% 4.16/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.16/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_34,negated_conjecture,
% 4.16/1.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
% 4.16/1.01      inference(cnf_transformation,[],[f108]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_0,plain,
% 4.16/1.01      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,X1) ),
% 4.16/1.01      inference(cnf_transformation,[],[f87]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2329,plain,
% 4.16/1.01      ( k2_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3))) = k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_34,c_0]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_21,plain,
% 4.16/1.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.16/1.01      inference(cnf_transformation,[],[f67]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2,plain,
% 4.16/1.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.16/1.01      inference(cnf_transformation,[],[f46]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1547,plain,
% 4.16/1.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_21,c_2]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2348,plain,
% 4.16/1.01      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_2329,c_1547]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_11,plain,
% 4.16/1.01      ( r2_hidden(X0,X1)
% 4.16/1.01      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 4.16/1.01      inference(cnf_transformation,[],[f111]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1110,plain,
% 4.16/1.01      ( r2_hidden(X0,X1) = iProver_top
% 4.16/1.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_12197,plain,
% 4.16/1.01      ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 4.16/1.01      | r2_hidden(X0,k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_2348,c_1110]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_12461,plain,
% 4.16/1.01      ( r2_hidden(sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 4.16/1.01      | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_1117,c_12197]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_29,plain,
% 4.16/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 4.16/1.01      inference(cnf_transformation,[],[f116]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1097,plain,
% 4.16/1.01      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_12593,plain,
% 4.16/1.01      ( sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = sK4
% 4.16/1.01      | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_12461,c_1097]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1,plain,
% 4.16/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 4.16/1.01      inference(cnf_transformation,[],[f88]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2683,plain,
% 4.16/1.01      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3) ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_2348,c_1]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_22,plain,
% 4.16/1.01      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
% 4.16/1.01      | k1_xboole_0 = X0 ),
% 4.16/1.01      inference(cnf_transformation,[],[f97]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1101,plain,
% 4.16/1.01      ( k1_xboole_0 = X0
% 4.16/1.01      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_6267,plain,
% 4.16/1.01      ( k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0
% 4.16/1.01      | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) != iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_2683,c_1101]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_12862,plain,
% 4.16/1.01      ( sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = sK4
% 4.16/1.01      | k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_12593,c_6267]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_32,negated_conjecture,
% 4.16/1.01      ( k2_enumset1(sK4,sK4,sK4,sK4) != sK3 ),
% 4.16/1.01      inference(cnf_transformation,[],[f107]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_16,plain,
% 4.16/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.16/1.01      inference(cnf_transformation,[],[f63]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1146,plain,
% 4.16/1.01      ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 4.16/1.01      | ~ r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 4.16/1.01      | k2_enumset1(sK4,sK4,sK4,sK4) = sK3 ),
% 4.16/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1147,plain,
% 4.16/1.01      ( k2_enumset1(sK4,sK4,sK4,sK4) = sK3
% 4.16/1.01      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
% 4.16/1.01      | r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_1146]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_20,plain,
% 4.16/1.01      ( r1_tarski(X0,X1)
% 4.16/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 4.16/1.01      inference(cnf_transformation,[],[f96]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1307,plain,
% 4.16/1.01      ( r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 4.16/1.01      | k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != k1_xboole_0 ),
% 4.16/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1314,plain,
% 4.16/1.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != k1_xboole_0
% 4.16/1.01      | r1_tarski(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1102,plain,
% 4.16/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 4.16/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_7213,plain,
% 4.16/1.01      ( k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != k1_xboole_0
% 4.16/1.01      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_2348,c_1102]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_16116,plain,
% 4.16/1.01      ( sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = sK4 ),
% 4.16/1.01      inference(global_propositional_subsumption,
% 4.16/1.01                [status(thm)],
% 4.16/1.01                [c_12862,c_34,c_32,c_1147,c_1314,c_7213]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_10,plain,
% 4.16/1.01      ( ~ r2_hidden(X0,X1)
% 4.16/1.01      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 4.16/1.01      inference(cnf_transformation,[],[f110]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1111,plain,
% 4.16/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.16/1.01      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 4.16/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_13169,plain,
% 4.16/1.01      ( r2_hidden(X0,k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
% 4.16/1.01      | r2_hidden(X0,sK3) != iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_2348,c_1111]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_14427,plain,
% 4.16/1.01      ( r2_hidden(sK0(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0),sK3) != iProver_top
% 4.16/1.01      | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0) = iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_1117,c_13169]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_16122,plain,
% 4.16/1.01      ( r2_hidden(sK4,sK3) != iProver_top
% 4.16/1.01      | r1_tarski(k5_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK3)) = iProver_top ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_16116,c_14427]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_16128,plain,
% 4.16/1.01      ( r2_hidden(sK4,sK3) != iProver_top ),
% 4.16/1.01      inference(global_propositional_subsumption,
% 4.16/1.01                [status(thm)],
% 4.16/1.01                [c_16122,c_34,c_32,c_1147,c_1314,c_6267,c_7213]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_16132,plain,
% 4.16/1.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = sK3 ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_1096,c_16128]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2211,plain,
% 4.16/1.01      ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0)) ),
% 4.16/1.01      inference(superposition,[status(thm)],[c_34,c_1]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_24,plain,
% 4.16/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 4.16/1.01      inference(cnf_transformation,[],[f99]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2214,plain,
% 4.16/1.01      ( k3_xboole_0(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = sK3 ),
% 4.16/1.01      inference(demodulation,[status(thm)],[c_2211,c_24]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_2404,plain,
% 4.16/1.01      ( k5_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 4.16/1.01      inference(demodulation,[status(thm)],[c_2214,c_34]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_16133,plain,
% 4.16/1.01      ( sK3 = k1_xboole_0 ),
% 4.16/1.01      inference(light_normalisation,
% 4.16/1.01                [status(thm)],
% 4.16/1.01                [c_16132,c_2214,c_2404]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_572,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1172,plain,
% 4.16/1.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 4.16/1.01      inference(instantiation,[status(thm)],[c_572]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_1173,plain,
% 4.16/1.01      ( sK3 != k1_xboole_0
% 4.16/1.01      | k1_xboole_0 = sK3
% 4.16/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.16/1.01      inference(instantiation,[status(thm)],[c_1172]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_28,plain,
% 4.16/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 4.16/1.01      inference(cnf_transformation,[],[f115]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_45,plain,
% 4.16/1.01      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 4.16/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_42,plain,
% 4.16/1.01      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 4.16/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 4.16/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(c_33,negated_conjecture,
% 4.16/1.01      ( k1_xboole_0 != sK3 ),
% 4.16/1.01      inference(cnf_transformation,[],[f83]) ).
% 4.16/1.01  
% 4.16/1.01  cnf(contradiction,plain,
% 4.16/1.01      ( $false ),
% 4.16/1.01      inference(minisat,[status(thm)],[c_16133,c_1173,c_45,c_42,c_33]) ).
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.16/1.01  
% 4.16/1.01  ------                               Statistics
% 4.16/1.01  
% 4.16/1.01  ------ General
% 4.16/1.01  
% 4.16/1.01  abstr_ref_over_cycles:                  0
% 4.16/1.01  abstr_ref_under_cycles:                 0
% 4.16/1.01  gc_basic_clause_elim:                   0
% 4.16/1.01  forced_gc_time:                         0
% 4.16/1.01  parsing_time:                           0.01
% 4.16/1.01  unif_index_cands_time:                  0.
% 4.16/1.01  unif_index_add_time:                    0.
% 4.16/1.01  orderings_time:                         0.
% 4.16/1.01  out_proof_time:                         0.01
% 4.16/1.01  total_time:                             0.476
% 4.16/1.01  num_of_symbols:                         43
% 4.16/1.01  num_of_terms:                           14667
% 4.16/1.01  
% 4.16/1.01  ------ Preprocessing
% 4.16/1.01  
% 4.16/1.01  num_of_splits:                          0
% 4.16/1.01  num_of_split_atoms:                     0
% 4.16/1.01  num_of_reused_defs:                     0
% 4.16/1.01  num_eq_ax_congr_red:                    24
% 4.16/1.01  num_of_sem_filtered_clauses:            1
% 4.16/1.01  num_of_subtypes:                        0
% 4.16/1.01  monotx_restored_types:                  0
% 4.16/1.01  sat_num_of_epr_types:                   0
% 4.16/1.01  sat_num_of_non_cyclic_types:            0
% 4.16/1.01  sat_guarded_non_collapsed_types:        0
% 4.16/1.01  num_pure_diseq_elim:                    0
% 4.16/1.01  simp_replaced_by:                       0
% 4.16/1.01  res_preprocessed:                       153
% 4.16/1.01  prep_upred:                             0
% 4.16/1.01  prep_unflattend:                        0
% 4.16/1.01  smt_new_axioms:                         0
% 4.16/1.01  pred_elim_cands:                        2
% 4.16/1.01  pred_elim:                              0
% 4.16/1.01  pred_elim_cl:                           0
% 4.16/1.01  pred_elim_cycles:                       2
% 4.16/1.01  merged_defs:                            16
% 4.16/1.01  merged_defs_ncl:                        0
% 4.16/1.01  bin_hyper_res:                          16
% 4.16/1.01  prep_cycles:                            4
% 4.16/1.01  pred_elim_time:                         0.
% 4.16/1.01  splitting_time:                         0.
% 4.16/1.01  sem_filter_time:                        0.
% 4.16/1.01  monotx_time:                            0.001
% 4.16/1.01  subtype_inf_time:                       0.
% 4.16/1.01  
% 4.16/1.01  ------ Problem properties
% 4.16/1.01  
% 4.16/1.01  clauses:                                34
% 4.16/1.01  conjectures:                            3
% 4.16/1.01  epr:                                    4
% 4.16/1.01  horn:                                   24
% 4.16/1.01  ground:                                 3
% 4.16/1.01  unary:                                  12
% 4.16/1.01  binary:                                 10
% 4.16/1.01  lits:                                   69
% 4.16/1.01  lits_eq:                                24
% 4.16/1.01  fd_pure:                                0
% 4.16/1.01  fd_pseudo:                              0
% 4.16/1.01  fd_cond:                                1
% 4.16/1.01  fd_pseudo_cond:                         6
% 4.16/1.01  ac_symbols:                             0
% 4.16/1.01  
% 4.16/1.01  ------ Propositional Solver
% 4.16/1.01  
% 4.16/1.01  prop_solver_calls:                      30
% 4.16/1.01  prop_fast_solver_calls:                 892
% 4.16/1.01  smt_solver_calls:                       0
% 4.16/1.01  smt_fast_solver_calls:                  0
% 4.16/1.01  prop_num_of_clauses:                    6455
% 4.16/1.01  prop_preprocess_simplified:             15954
% 4.16/1.01  prop_fo_subsumed:                       8
% 4.16/1.01  prop_solver_time:                       0.
% 4.16/1.01  smt_solver_time:                        0.
% 4.16/1.01  smt_fast_solver_time:                   0.
% 4.16/1.01  prop_fast_solver_time:                  0.
% 4.16/1.01  prop_unsat_core_time:                   0.
% 4.16/1.01  
% 4.16/1.01  ------ QBF
% 4.16/1.01  
% 4.16/1.01  qbf_q_res:                              0
% 4.16/1.01  qbf_num_tautologies:                    0
% 4.16/1.01  qbf_prep_cycles:                        0
% 4.16/1.01  
% 4.16/1.01  ------ BMC1
% 4.16/1.01  
% 4.16/1.01  bmc1_current_bound:                     -1
% 4.16/1.01  bmc1_last_solved_bound:                 -1
% 4.16/1.01  bmc1_unsat_core_size:                   -1
% 4.16/1.01  bmc1_unsat_core_parents_size:           -1
% 4.16/1.01  bmc1_merge_next_fun:                    0
% 4.16/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.16/1.01  
% 4.16/1.01  ------ Instantiation
% 4.16/1.01  
% 4.16/1.01  inst_num_of_clauses:                    1773
% 4.16/1.01  inst_num_in_passive:                    938
% 4.16/1.01  inst_num_in_active:                     529
% 4.16/1.01  inst_num_in_unprocessed:                308
% 4.16/1.01  inst_num_of_loops:                      710
% 4.16/1.01  inst_num_of_learning_restarts:          0
% 4.16/1.01  inst_num_moves_active_passive:          181
% 4.16/1.01  inst_lit_activity:                      0
% 4.16/1.01  inst_lit_activity_moves:                0
% 4.16/1.01  inst_num_tautologies:                   0
% 4.16/1.01  inst_num_prop_implied:                  0
% 4.16/1.01  inst_num_existing_simplified:           0
% 4.16/1.01  inst_num_eq_res_simplified:             0
% 4.16/1.01  inst_num_child_elim:                    0
% 4.16/1.01  inst_num_of_dismatching_blockings:      985
% 4.16/1.01  inst_num_of_non_proper_insts:           1824
% 4.16/1.01  inst_num_of_duplicates:                 0
% 4.16/1.01  inst_inst_num_from_inst_to_res:         0
% 4.16/1.01  inst_dismatching_checking_time:         0.
% 4.16/1.01  
% 4.16/1.01  ------ Resolution
% 4.16/1.01  
% 4.16/1.01  res_num_of_clauses:                     0
% 4.16/1.01  res_num_in_passive:                     0
% 4.16/1.01  res_num_in_active:                      0
% 4.16/1.01  res_num_of_loops:                       157
% 4.16/1.01  res_forward_subset_subsumed:            112
% 4.16/1.01  res_backward_subset_subsumed:           4
% 4.16/1.01  res_forward_subsumed:                   0
% 4.16/1.01  res_backward_subsumed:                  0
% 4.16/1.01  res_forward_subsumption_resolution:     0
% 4.16/1.01  res_backward_subsumption_resolution:    0
% 4.16/1.01  res_clause_to_clause_subsumption:       3054
% 4.16/1.01  res_orphan_elimination:                 0
% 4.16/1.01  res_tautology_del:                      127
% 4.16/1.01  res_num_eq_res_simplified:              0
% 4.16/1.01  res_num_sel_changes:                    0
% 4.16/1.01  res_moves_from_active_to_pass:          0
% 4.16/1.01  
% 4.16/1.01  ------ Superposition
% 4.16/1.01  
% 4.16/1.01  sup_time_total:                         0.
% 4.16/1.01  sup_time_generating:                    0.
% 4.16/1.01  sup_time_sim_full:                      0.
% 4.16/1.01  sup_time_sim_immed:                     0.
% 4.16/1.01  
% 4.16/1.01  sup_num_of_clauses:                     420
% 4.16/1.01  sup_num_in_active:                      120
% 4.16/1.01  sup_num_in_passive:                     300
% 4.16/1.01  sup_num_of_loops:                       141
% 4.16/1.01  sup_fw_superposition:                   1191
% 4.16/1.01  sup_bw_superposition:                   695
% 4.16/1.01  sup_immediate_simplified:               1064
% 4.16/1.01  sup_given_eliminated:                   4
% 4.16/1.01  comparisons_done:                       0
% 4.16/1.01  comparisons_avoided:                    10
% 4.16/1.01  
% 4.16/1.01  ------ Simplifications
% 4.16/1.01  
% 4.16/1.01  
% 4.16/1.01  sim_fw_subset_subsumed:                 31
% 4.16/1.01  sim_bw_subset_subsumed:                 11
% 4.16/1.01  sim_fw_subsumed:                        136
% 4.16/1.01  sim_bw_subsumed:                        13
% 4.16/1.01  sim_fw_subsumption_res:                 0
% 4.16/1.01  sim_bw_subsumption_res:                 0
% 4.16/1.01  sim_tautology_del:                      42
% 4.16/1.01  sim_eq_tautology_del:                   314
% 4.16/1.01  sim_eq_res_simp:                        17
% 4.16/1.01  sim_fw_demodulated:                     621
% 4.16/1.01  sim_bw_demodulated:                     24
% 4.16/1.01  sim_light_normalised:                   598
% 4.16/1.01  sim_joinable_taut:                      0
% 4.16/1.01  sim_joinable_simp:                      0
% 4.16/1.01  sim_ac_normalised:                      0
% 4.16/1.01  sim_smt_subsumption:                    0
% 4.16/1.01  
%------------------------------------------------------------------------------
