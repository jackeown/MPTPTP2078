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
% DateTime   : Thu Dec  3 11:29:13 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 213 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  234 ( 458 expanded)
%              Number of equality atoms :  177 ( 363 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f31,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( sK4 != sK5
    & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f45])).

fof(f80,plain,(
    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f86,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f103,plain,(
    k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f80,f82,f87,f87,f87])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f72,f82,f78,f87])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f85])).

fof(f104,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f105,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f104])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f113,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f87])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f101])).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f81,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1351,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_26,c_0])).

cnf(c_16,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_482,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12171,plain,
    ( r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_482])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_726,plain,
    ( ~ r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_727,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_654,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_655,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_22,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_32,plain,
    ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12171,c_729,c_655,c_32,c_29,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:15:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.84/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.00  
% 3.84/1.00  ------  iProver source info
% 3.84/1.00  
% 3.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.00  git: non_committed_changes: false
% 3.84/1.00  git: last_make_outside_of_git: false
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    --mode clausify
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             sel
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         604.99
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              none
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           false
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             false
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         false
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     num_symb
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       true
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     false
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   []
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_full_bw                           [BwDemod]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  ------ Parsing...
% 3.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  ------ Proving...
% 3.84/1.00  ------ Problem Properties 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  clauses                                 27
% 3.84/1.00  conjectures                             2
% 3.84/1.00  EPR                                     1
% 3.84/1.00  Horn                                    22
% 3.84/1.00  unary                                   15
% 3.84/1.00  binary                                  5
% 3.84/1.00  lits                                    49
% 3.84/1.00  lits eq                                 29
% 3.84/1.00  fd_pure                                 0
% 3.84/1.00  fd_pseudo                               0
% 3.84/1.00  fd_cond                                 1
% 3.84/1.00  fd_pseudo_cond                          6
% 3.84/1.00  AC symbols                              1
% 3.84/1.00  
% 3.84/1.00  ------ Input Options Time Limit: Unbounded
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  Current options:
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    --mode clausify
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             sel
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         604.99
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              none
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           false
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             false
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         false
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     num_symb
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       true
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     false
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   []
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_full_bw                           [BwDemod]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS status Theorem for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  fof(f23,conjecture,(
% 3.84/1.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f24,negated_conjecture,(
% 3.84/1.00    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.84/1.00    inference(negated_conjecture,[],[f23])).
% 3.84/1.00  
% 3.84/1.00  fof(f31,plain,(
% 3.84/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f45,plain,(
% 3.84/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f46,plain,(
% 3.84/1.00    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f45])).
% 3.84/1.00  
% 3.84/1.00  fof(f80,plain,(
% 3.84/1.00    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.84/1.00    inference(cnf_transformation,[],[f46])).
% 3.84/1.00  
% 3.84/1.00  fof(f12,axiom,(
% 3.84/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f59,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f12])).
% 3.84/1.00  
% 3.84/1.00  fof(f6,axiom,(
% 3.84/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f53,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f6])).
% 3.84/1.00  
% 3.84/1.00  fof(f82,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f59,f53])).
% 3.84/1.00  
% 3.84/1.00  fof(f16,axiom,(
% 3.84/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f73,plain,(
% 3.84/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  fof(f17,axiom,(
% 3.84/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f74,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f17])).
% 3.84/1.00  
% 3.84/1.00  fof(f18,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f75,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f19,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f76,plain,(
% 3.84/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f19])).
% 3.84/1.00  
% 3.84/1.00  fof(f20,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f77,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f20])).
% 3.84/1.00  
% 3.84/1.00  fof(f21,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f78,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f21])).
% 3.84/1.00  
% 3.84/1.00  fof(f83,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f77,f78])).
% 3.84/1.00  
% 3.84/1.00  fof(f84,plain,(
% 3.84/1.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f76,f83])).
% 3.84/1.00  
% 3.84/1.00  fof(f85,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f75,f84])).
% 3.84/1.00  
% 3.84/1.00  fof(f86,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f74,f85])).
% 3.84/1.00  
% 3.84/1.00  fof(f87,plain,(
% 3.84/1.00    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f73,f86])).
% 3.84/1.00  
% 3.84/1.00  fof(f103,plain,(
% 3.84/1.00    k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 3.84/1.00    inference(definition_unfolding,[],[f80,f82,f87,f87,f87])).
% 3.84/1.00  
% 3.84/1.00  fof(f15,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f72,plain,(
% 3.84/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f88,plain,(
% 3.84/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f72,f82,f78,f87])).
% 3.84/1.00  
% 3.84/1.00  fof(f13,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f30,plain,(
% 3.84/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.84/1.00    inference(ennf_transformation,[],[f13])).
% 3.84/1.00  
% 3.84/1.00  fof(f36,plain,(
% 3.84/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/1.00    inference(nnf_transformation,[],[f30])).
% 3.84/1.00  
% 3.84/1.00  fof(f37,plain,(
% 3.84/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/1.00    inference(flattening,[],[f36])).
% 3.84/1.00  
% 3.84/1.00  fof(f38,plain,(
% 3.84/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/1.00    inference(rectify,[],[f37])).
% 3.84/1.00  
% 3.84/1.00  fof(f39,plain,(
% 3.84/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f40,plain,(
% 3.84/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 3.84/1.00  
% 3.84/1.00  fof(f63,plain,(
% 3.84/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.84/1.00    inference(cnf_transformation,[],[f40])).
% 3.84/1.00  
% 3.84/1.00  fof(f95,plain,(
% 3.84/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.84/1.00    inference(definition_unfolding,[],[f63,f85])).
% 3.84/1.00  
% 3.84/1.00  fof(f104,plain,(
% 3.84/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.84/1.00    inference(equality_resolution,[],[f95])).
% 3.84/1.00  
% 3.84/1.00  fof(f105,plain,(
% 3.84/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 3.84/1.00    inference(equality_resolution,[],[f104])).
% 3.84/1.00  
% 3.84/1.00  fof(f14,axiom,(
% 3.84/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f41,plain,(
% 3.84/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.84/1.00    inference(nnf_transformation,[],[f14])).
% 3.84/1.00  
% 3.84/1.00  fof(f42,plain,(
% 3.84/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.84/1.00    inference(rectify,[],[f41])).
% 3.84/1.00  
% 3.84/1.00  fof(f43,plain,(
% 3.84/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f44,plain,(
% 3.84/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 3.84/1.00  
% 3.84/1.00  fof(f68,plain,(
% 3.84/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.84/1.00    inference(cnf_transformation,[],[f44])).
% 3.84/1.00  
% 3.84/1.00  fof(f102,plain,(
% 3.84/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.84/1.00    inference(definition_unfolding,[],[f68,f87])).
% 3.84/1.00  
% 3.84/1.00  fof(f113,plain,(
% 3.84/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 3.84/1.00    inference(equality_resolution,[],[f102])).
% 3.84/1.00  
% 3.84/1.00  fof(f69,plain,(
% 3.84/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.84/1.00    inference(cnf_transformation,[],[f44])).
% 3.84/1.00  
% 3.84/1.00  fof(f101,plain,(
% 3.84/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.84/1.00    inference(definition_unfolding,[],[f69,f87])).
% 3.84/1.00  
% 3.84/1.00  fof(f111,plain,(
% 3.84/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 3.84/1.00    inference(equality_resolution,[],[f101])).
% 3.84/1.00  
% 3.84/1.00  fof(f112,plain,(
% 3.84/1.00    ( ! [X3] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) )),
% 3.84/1.00    inference(equality_resolution,[],[f111])).
% 3.84/1.00  
% 3.84/1.00  fof(f81,plain,(
% 3.84/1.00    sK4 != sK5),
% 3.84/1.00    inference(cnf_transformation,[],[f46])).
% 3.84/1.00  
% 3.84/1.00  cnf(c_26,negated_conjecture,
% 3.84/1.00      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.84/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_0,plain,
% 3.84/1.00      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.84/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1351,plain,
% 3.84/1.00      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_26,c_0]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_16,plain,
% 3.84/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_482,plain,
% 3.84/1.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12171,plain,
% 3.84/1.00      ( r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1351,c_482]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_23,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.84/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_726,plain,
% 3.84/1.00      ( ~ r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | sK5 = X0 ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_727,plain,
% 3.84/1.00      ( sK5 = X0
% 3.84/1.00      | r2_hidden(sK5,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_729,plain,
% 3.84/1.00      ( sK5 = sK4
% 3.84/1.00      | r2_hidden(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_727]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_654,plain,
% 3.84/1.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_182]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_655,plain,
% 3.84/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_654]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_22,plain,
% 3.84/1.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_32,plain,
% 3.84/1.00      ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_29,plain,
% 3.84/1.00      ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.84/1.00      | sK4 = sK4 ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_25,negated_conjecture,
% 3.84/1.00      ( sK4 != sK5 ),
% 3.84/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(contradiction,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(minisat,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_12171,c_729,c_655,c_32,c_29,c_25]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ Selected
% 3.84/1.00  
% 3.84/1.00  total_time:                             0.477
% 3.84/1.00  
%------------------------------------------------------------------------------
