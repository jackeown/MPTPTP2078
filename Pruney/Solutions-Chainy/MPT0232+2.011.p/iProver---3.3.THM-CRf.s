%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:12 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 343 expanded)
%              Number of clauses        :   45 (  55 expanded)
%              Number of leaves         :   27 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 ( 559 expanded)
%              Number of equality atoms :  230 ( 451 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f24])).

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

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f76])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f77])).

fof(f102,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f103,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f102])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k1_tarski(X2) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k1_tarski(X2) = k2_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k2_tarski(X0,X1)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X2) != k2_tarski(X0,X1)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k1_tarski(sK4) != k2_tarski(sK2,sK3)
      & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k1_tarski(sK4) != k2_tarski(sK2,sK3)
    & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f37])).

fof(f71,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f64,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f95,plain,(
    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f71,f78,f79])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f62,f73,f69,f79])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f107,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f20,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f79,f78])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    k1_tarski(sK4) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f72,f79,f78])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1640,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1633,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1647,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15163,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1633,c_1647])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2126,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_60416,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_15163,c_2126])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1756,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_2])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2051,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_2048,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1888,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_2])).

cnf(c_2058,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_2048,c_1888])).

cnf(c_2314,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2051,c_2058])).

cnf(c_2332,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2314,c_7])).

cnf(c_2833,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_1756,c_2332])).

cnf(c_66172,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_60416,c_2833])).

cnf(c_66189,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_66172,c_9,c_1888])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1635,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_66936,plain,
    ( sK4 = X0
    | r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_66189,c_1635])).

cnf(c_95631,plain,
    ( sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_1640,c_66936])).

cnf(c_1355,plain,
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

cnf(c_2078,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
    | sK4 != X0
    | sK4 != X1
    | sK4 != X2
    | sK4 != X3
    | sK4 != X4
    | sK4 != X5
    | sK4 != X6
    | sK4 != X7 ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_21168,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_1358,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1823,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_2077,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != X8 ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_3420,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_9183,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3420])).

cnf(c_22,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3746,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1353,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1881,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1779,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_23,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_95631,c_21168,c_9183,c_3746,c_1881,c_1779,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 23.66/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.66/3.49  
% 23.66/3.49  ------  iProver source info
% 23.66/3.49  
% 23.66/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.66/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.66/3.49  git: non_committed_changes: false
% 23.66/3.49  git: last_make_outside_of_git: false
% 23.66/3.49  
% 23.66/3.49  ------ 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options
% 23.66/3.49  
% 23.66/3.49  --out_options                           all
% 23.66/3.49  --tptp_safe_out                         true
% 23.66/3.49  --problem_path                          ""
% 23.66/3.49  --include_path                          ""
% 23.66/3.49  --clausifier                            res/vclausify_rel
% 23.66/3.49  --clausifier_options                    --mode clausify
% 23.66/3.49  --stdin                                 false
% 23.66/3.49  --stats_out                             all
% 23.66/3.49  
% 23.66/3.49  ------ General Options
% 23.66/3.49  
% 23.66/3.49  --fof                                   false
% 23.66/3.49  --time_out_real                         305.
% 23.66/3.49  --time_out_virtual                      -1.
% 23.66/3.49  --symbol_type_check                     false
% 23.66/3.49  --clausify_out                          false
% 23.66/3.49  --sig_cnt_out                           false
% 23.66/3.49  --trig_cnt_out                          false
% 23.66/3.49  --trig_cnt_out_tolerance                1.
% 23.66/3.49  --trig_cnt_out_sk_spl                   false
% 23.66/3.49  --abstr_cl_out                          false
% 23.66/3.49  
% 23.66/3.49  ------ Global Options
% 23.66/3.49  
% 23.66/3.49  --schedule                              default
% 23.66/3.49  --add_important_lit                     false
% 23.66/3.49  --prop_solver_per_cl                    1000
% 23.66/3.49  --min_unsat_core                        false
% 23.66/3.49  --soft_assumptions                      false
% 23.66/3.49  --soft_lemma_size                       3
% 23.66/3.49  --prop_impl_unit_size                   0
% 23.66/3.49  --prop_impl_unit                        []
% 23.66/3.49  --share_sel_clauses                     true
% 23.66/3.49  --reset_solvers                         false
% 23.66/3.49  --bc_imp_inh                            [conj_cone]
% 23.66/3.49  --conj_cone_tolerance                   3.
% 23.66/3.49  --extra_neg_conj                        none
% 23.66/3.49  --large_theory_mode                     true
% 23.66/3.49  --prolific_symb_bound                   200
% 23.66/3.49  --lt_threshold                          2000
% 23.66/3.49  --clause_weak_htbl                      true
% 23.66/3.49  --gc_record_bc_elim                     false
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing Options
% 23.66/3.49  
% 23.66/3.49  --preprocessing_flag                    true
% 23.66/3.49  --time_out_prep_mult                    0.1
% 23.66/3.49  --splitting_mode                        input
% 23.66/3.49  --splitting_grd                         true
% 23.66/3.49  --splitting_cvd                         false
% 23.66/3.49  --splitting_cvd_svl                     false
% 23.66/3.49  --splitting_nvd                         32
% 23.66/3.49  --sub_typing                            true
% 23.66/3.49  --prep_gs_sim                           true
% 23.66/3.49  --prep_unflatten                        true
% 23.66/3.49  --prep_res_sim                          true
% 23.66/3.49  --prep_upred                            true
% 23.66/3.49  --prep_sem_filter                       exhaustive
% 23.66/3.49  --prep_sem_filter_out                   false
% 23.66/3.49  --pred_elim                             true
% 23.66/3.49  --res_sim_input                         true
% 23.66/3.49  --eq_ax_congr_red                       true
% 23.66/3.49  --pure_diseq_elim                       true
% 23.66/3.49  --brand_transform                       false
% 23.66/3.49  --non_eq_to_eq                          false
% 23.66/3.49  --prep_def_merge                        true
% 23.66/3.49  --prep_def_merge_prop_impl              false
% 23.66/3.49  --prep_def_merge_mbd                    true
% 23.66/3.49  --prep_def_merge_tr_red                 false
% 23.66/3.49  --prep_def_merge_tr_cl                  false
% 23.66/3.49  --smt_preprocessing                     true
% 23.66/3.49  --smt_ac_axioms                         fast
% 23.66/3.49  --preprocessed_out                      false
% 23.66/3.49  --preprocessed_stats                    false
% 23.66/3.49  
% 23.66/3.49  ------ Abstraction refinement Options
% 23.66/3.49  
% 23.66/3.49  --abstr_ref                             []
% 23.66/3.49  --abstr_ref_prep                        false
% 23.66/3.49  --abstr_ref_until_sat                   false
% 23.66/3.49  --abstr_ref_sig_restrict                funpre
% 23.66/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.49  --abstr_ref_under                       []
% 23.66/3.49  
% 23.66/3.49  ------ SAT Options
% 23.66/3.49  
% 23.66/3.49  --sat_mode                              false
% 23.66/3.49  --sat_fm_restart_options                ""
% 23.66/3.49  --sat_gr_def                            false
% 23.66/3.49  --sat_epr_types                         true
% 23.66/3.49  --sat_non_cyclic_types                  false
% 23.66/3.49  --sat_finite_models                     false
% 23.66/3.49  --sat_fm_lemmas                         false
% 23.66/3.49  --sat_fm_prep                           false
% 23.66/3.50  --sat_fm_uc_incr                        true
% 23.66/3.50  --sat_out_model                         small
% 23.66/3.50  --sat_out_clauses                       false
% 23.66/3.50  
% 23.66/3.50  ------ QBF Options
% 23.66/3.50  
% 23.66/3.50  --qbf_mode                              false
% 23.66/3.50  --qbf_elim_univ                         false
% 23.66/3.50  --qbf_dom_inst                          none
% 23.66/3.50  --qbf_dom_pre_inst                      false
% 23.66/3.50  --qbf_sk_in                             false
% 23.66/3.50  --qbf_pred_elim                         true
% 23.66/3.50  --qbf_split                             512
% 23.66/3.50  
% 23.66/3.50  ------ BMC1 Options
% 23.66/3.50  
% 23.66/3.50  --bmc1_incremental                      false
% 23.66/3.50  --bmc1_axioms                           reachable_all
% 23.66/3.50  --bmc1_min_bound                        0
% 23.66/3.50  --bmc1_max_bound                        -1
% 23.66/3.50  --bmc1_max_bound_default                -1
% 23.66/3.50  --bmc1_symbol_reachability              true
% 23.66/3.50  --bmc1_property_lemmas                  false
% 23.66/3.50  --bmc1_k_induction                      false
% 23.66/3.50  --bmc1_non_equiv_states                 false
% 23.66/3.50  --bmc1_deadlock                         false
% 23.66/3.50  --bmc1_ucm                              false
% 23.66/3.50  --bmc1_add_unsat_core                   none
% 23.66/3.50  --bmc1_unsat_core_children              false
% 23.66/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.50  --bmc1_out_stat                         full
% 23.66/3.50  --bmc1_ground_init                      false
% 23.66/3.50  --bmc1_pre_inst_next_state              false
% 23.66/3.50  --bmc1_pre_inst_state                   false
% 23.66/3.50  --bmc1_pre_inst_reach_state             false
% 23.66/3.50  --bmc1_out_unsat_core                   false
% 23.66/3.50  --bmc1_aig_witness_out                  false
% 23.66/3.50  --bmc1_verbose                          false
% 23.66/3.50  --bmc1_dump_clauses_tptp                false
% 23.66/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.50  --bmc1_dump_file                        -
% 23.66/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.50  --bmc1_ucm_extend_mode                  1
% 23.66/3.50  --bmc1_ucm_init_mode                    2
% 23.66/3.50  --bmc1_ucm_cone_mode                    none
% 23.66/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.50  --bmc1_ucm_relax_model                  4
% 23.66/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.50  --bmc1_ucm_layered_model                none
% 23.66/3.50  --bmc1_ucm_max_lemma_size               10
% 23.66/3.50  
% 23.66/3.50  ------ AIG Options
% 23.66/3.50  
% 23.66/3.50  --aig_mode                              false
% 23.66/3.50  
% 23.66/3.50  ------ Instantiation Options
% 23.66/3.50  
% 23.66/3.50  --instantiation_flag                    true
% 23.66/3.50  --inst_sos_flag                         false
% 23.66/3.50  --inst_sos_phase                        true
% 23.66/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.50  --inst_lit_sel_side                     num_symb
% 23.66/3.50  --inst_solver_per_active                1400
% 23.66/3.50  --inst_solver_calls_frac                1.
% 23.66/3.50  --inst_passive_queue_type               priority_queues
% 23.66/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.50  --inst_passive_queues_freq              [25;2]
% 23.66/3.50  --inst_dismatching                      true
% 23.66/3.50  --inst_eager_unprocessed_to_passive     true
% 23.66/3.50  --inst_prop_sim_given                   true
% 23.66/3.50  --inst_prop_sim_new                     false
% 23.66/3.50  --inst_subs_new                         false
% 23.66/3.50  --inst_eq_res_simp                      false
% 23.66/3.50  --inst_subs_given                       false
% 23.66/3.50  --inst_orphan_elimination               true
% 23.66/3.50  --inst_learning_loop_flag               true
% 23.66/3.50  --inst_learning_start                   3000
% 23.66/3.50  --inst_learning_factor                  2
% 23.66/3.50  --inst_start_prop_sim_after_learn       3
% 23.66/3.50  --inst_sel_renew                        solver
% 23.66/3.50  --inst_lit_activity_flag                true
% 23.66/3.50  --inst_restr_to_given                   false
% 23.66/3.50  --inst_activity_threshold               500
% 23.66/3.50  --inst_out_proof                        true
% 23.66/3.50  
% 23.66/3.50  ------ Resolution Options
% 23.66/3.50  
% 23.66/3.50  --resolution_flag                       true
% 23.66/3.50  --res_lit_sel                           adaptive
% 23.66/3.50  --res_lit_sel_side                      none
% 23.66/3.50  --res_ordering                          kbo
% 23.66/3.50  --res_to_prop_solver                    active
% 23.66/3.50  --res_prop_simpl_new                    false
% 23.66/3.50  --res_prop_simpl_given                  true
% 23.66/3.50  --res_passive_queue_type                priority_queues
% 23.66/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.50  --res_passive_queues_freq               [15;5]
% 23.66/3.50  --res_forward_subs                      full
% 23.66/3.50  --res_backward_subs                     full
% 23.66/3.50  --res_forward_subs_resolution           true
% 23.66/3.50  --res_backward_subs_resolution          true
% 23.66/3.50  --res_orphan_elimination                true
% 23.66/3.50  --res_time_limit                        2.
% 23.66/3.50  --res_out_proof                         true
% 23.66/3.50  
% 23.66/3.50  ------ Superposition Options
% 23.66/3.50  
% 23.66/3.50  --superposition_flag                    true
% 23.66/3.50  --sup_passive_queue_type                priority_queues
% 23.66/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.50  --demod_completeness_check              fast
% 23.66/3.50  --demod_use_ground                      true
% 23.66/3.50  --sup_to_prop_solver                    passive
% 23.66/3.50  --sup_prop_simpl_new                    true
% 23.66/3.50  --sup_prop_simpl_given                  true
% 23.66/3.50  --sup_fun_splitting                     false
% 23.66/3.50  --sup_smt_interval                      50000
% 23.66/3.50  
% 23.66/3.50  ------ Superposition Simplification Setup
% 23.66/3.50  
% 23.66/3.50  --sup_indices_passive                   []
% 23.66/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.66/3.50  --sup_full_bw                           [BwDemod]
% 23.66/3.50  --sup_immed_triv                        [TrivRules]
% 23.66/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.66/3.50  --sup_immed_bw_main                     []
% 23.66/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.66/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.66/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.66/3.50  
% 23.66/3.50  ------ Combination Options
% 23.66/3.50  
% 23.66/3.50  --comb_res_mult                         3
% 23.66/3.50  --comb_sup_mult                         2
% 23.66/3.50  --comb_inst_mult                        10
% 23.66/3.50  
% 23.66/3.50  ------ Debug Options
% 23.66/3.50  
% 23.66/3.50  --dbg_backtrace                         false
% 23.66/3.50  --dbg_dump_prop_clauses                 false
% 23.66/3.50  --dbg_dump_prop_clauses_file            -
% 23.66/3.50  --dbg_out_stat                          false
% 23.66/3.50  ------ Parsing...
% 23.66/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.66/3.50  ------ Proving...
% 23.66/3.50  ------ Problem Properties 
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  clauses                                 24
% 23.66/3.50  conjectures                             2
% 23.66/3.50  EPR                                     2
% 23.66/3.50  Horn                                    21
% 23.66/3.50  unary                                   14
% 23.66/3.50  binary                                  2
% 23.66/3.50  lits                                    45
% 23.66/3.50  lits eq                                 27
% 23.66/3.50  fd_pure                                 0
% 23.66/3.50  fd_pseudo                               0
% 23.66/3.50  fd_cond                                 0
% 23.66/3.50  fd_pseudo_cond                          7
% 23.66/3.50  AC symbols                              1
% 23.66/3.50  
% 23.66/3.50  ------ Schedule dynamic 5 is on 
% 23.66/3.50  
% 23.66/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  ------ 
% 23.66/3.50  Current options:
% 23.66/3.50  ------ 
% 23.66/3.50  
% 23.66/3.50  ------ Input Options
% 23.66/3.50  
% 23.66/3.50  --out_options                           all
% 23.66/3.50  --tptp_safe_out                         true
% 23.66/3.50  --problem_path                          ""
% 23.66/3.50  --include_path                          ""
% 23.66/3.50  --clausifier                            res/vclausify_rel
% 23.66/3.50  --clausifier_options                    --mode clausify
% 23.66/3.50  --stdin                                 false
% 23.66/3.50  --stats_out                             all
% 23.66/3.50  
% 23.66/3.50  ------ General Options
% 23.66/3.50  
% 23.66/3.50  --fof                                   false
% 23.66/3.50  --time_out_real                         305.
% 23.66/3.50  --time_out_virtual                      -1.
% 23.66/3.50  --symbol_type_check                     false
% 23.66/3.50  --clausify_out                          false
% 23.66/3.50  --sig_cnt_out                           false
% 23.66/3.50  --trig_cnt_out                          false
% 23.66/3.50  --trig_cnt_out_tolerance                1.
% 23.66/3.50  --trig_cnt_out_sk_spl                   false
% 23.66/3.50  --abstr_cl_out                          false
% 23.66/3.50  
% 23.66/3.50  ------ Global Options
% 23.66/3.50  
% 23.66/3.50  --schedule                              default
% 23.66/3.50  --add_important_lit                     false
% 23.66/3.50  --prop_solver_per_cl                    1000
% 23.66/3.50  --min_unsat_core                        false
% 23.66/3.50  --soft_assumptions                      false
% 23.66/3.50  --soft_lemma_size                       3
% 23.66/3.50  --prop_impl_unit_size                   0
% 23.66/3.50  --prop_impl_unit                        []
% 23.66/3.50  --share_sel_clauses                     true
% 23.66/3.50  --reset_solvers                         false
% 23.66/3.50  --bc_imp_inh                            [conj_cone]
% 23.66/3.50  --conj_cone_tolerance                   3.
% 23.66/3.50  --extra_neg_conj                        none
% 23.66/3.50  --large_theory_mode                     true
% 23.66/3.50  --prolific_symb_bound                   200
% 23.66/3.50  --lt_threshold                          2000
% 23.66/3.50  --clause_weak_htbl                      true
% 23.66/3.50  --gc_record_bc_elim                     false
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing Options
% 23.66/3.50  
% 23.66/3.50  --preprocessing_flag                    true
% 23.66/3.50  --time_out_prep_mult                    0.1
% 23.66/3.50  --splitting_mode                        input
% 23.66/3.50  --splitting_grd                         true
% 23.66/3.50  --splitting_cvd                         false
% 23.66/3.50  --splitting_cvd_svl                     false
% 23.66/3.50  --splitting_nvd                         32
% 23.66/3.50  --sub_typing                            true
% 23.66/3.50  --prep_gs_sim                           true
% 23.66/3.50  --prep_unflatten                        true
% 23.66/3.50  --prep_res_sim                          true
% 23.66/3.50  --prep_upred                            true
% 23.66/3.50  --prep_sem_filter                       exhaustive
% 23.66/3.50  --prep_sem_filter_out                   false
% 23.66/3.50  --pred_elim                             true
% 23.66/3.50  --res_sim_input                         true
% 23.66/3.50  --eq_ax_congr_red                       true
% 23.66/3.50  --pure_diseq_elim                       true
% 23.66/3.50  --brand_transform                       false
% 23.66/3.50  --non_eq_to_eq                          false
% 23.66/3.50  --prep_def_merge                        true
% 23.66/3.50  --prep_def_merge_prop_impl              false
% 23.66/3.50  --prep_def_merge_mbd                    true
% 23.66/3.50  --prep_def_merge_tr_red                 false
% 23.66/3.50  --prep_def_merge_tr_cl                  false
% 23.66/3.50  --smt_preprocessing                     true
% 23.66/3.50  --smt_ac_axioms                         fast
% 23.66/3.50  --preprocessed_out                      false
% 23.66/3.50  --preprocessed_stats                    false
% 23.66/3.50  
% 23.66/3.50  ------ Abstraction refinement Options
% 23.66/3.50  
% 23.66/3.50  --abstr_ref                             []
% 23.66/3.50  --abstr_ref_prep                        false
% 23.66/3.50  --abstr_ref_until_sat                   false
% 23.66/3.50  --abstr_ref_sig_restrict                funpre
% 23.66/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.50  --abstr_ref_under                       []
% 23.66/3.50  
% 23.66/3.50  ------ SAT Options
% 23.66/3.50  
% 23.66/3.50  --sat_mode                              false
% 23.66/3.50  --sat_fm_restart_options                ""
% 23.66/3.50  --sat_gr_def                            false
% 23.66/3.50  --sat_epr_types                         true
% 23.66/3.50  --sat_non_cyclic_types                  false
% 23.66/3.50  --sat_finite_models                     false
% 23.66/3.50  --sat_fm_lemmas                         false
% 23.66/3.50  --sat_fm_prep                           false
% 23.66/3.50  --sat_fm_uc_incr                        true
% 23.66/3.50  --sat_out_model                         small
% 23.66/3.50  --sat_out_clauses                       false
% 23.66/3.50  
% 23.66/3.50  ------ QBF Options
% 23.66/3.50  
% 23.66/3.50  --qbf_mode                              false
% 23.66/3.50  --qbf_elim_univ                         false
% 23.66/3.50  --qbf_dom_inst                          none
% 23.66/3.50  --qbf_dom_pre_inst                      false
% 23.66/3.50  --qbf_sk_in                             false
% 23.66/3.50  --qbf_pred_elim                         true
% 23.66/3.50  --qbf_split                             512
% 23.66/3.50  
% 23.66/3.50  ------ BMC1 Options
% 23.66/3.50  
% 23.66/3.50  --bmc1_incremental                      false
% 23.66/3.50  --bmc1_axioms                           reachable_all
% 23.66/3.50  --bmc1_min_bound                        0
% 23.66/3.50  --bmc1_max_bound                        -1
% 23.66/3.50  --bmc1_max_bound_default                -1
% 23.66/3.50  --bmc1_symbol_reachability              true
% 23.66/3.50  --bmc1_property_lemmas                  false
% 23.66/3.50  --bmc1_k_induction                      false
% 23.66/3.50  --bmc1_non_equiv_states                 false
% 23.66/3.50  --bmc1_deadlock                         false
% 23.66/3.50  --bmc1_ucm                              false
% 23.66/3.50  --bmc1_add_unsat_core                   none
% 23.66/3.50  --bmc1_unsat_core_children              false
% 23.66/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.50  --bmc1_out_stat                         full
% 23.66/3.50  --bmc1_ground_init                      false
% 23.66/3.50  --bmc1_pre_inst_next_state              false
% 23.66/3.50  --bmc1_pre_inst_state                   false
% 23.66/3.50  --bmc1_pre_inst_reach_state             false
% 23.66/3.50  --bmc1_out_unsat_core                   false
% 23.66/3.50  --bmc1_aig_witness_out                  false
% 23.66/3.50  --bmc1_verbose                          false
% 23.66/3.50  --bmc1_dump_clauses_tptp                false
% 23.66/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.50  --bmc1_dump_file                        -
% 23.66/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.50  --bmc1_ucm_extend_mode                  1
% 23.66/3.50  --bmc1_ucm_init_mode                    2
% 23.66/3.50  --bmc1_ucm_cone_mode                    none
% 23.66/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.50  --bmc1_ucm_relax_model                  4
% 23.66/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.50  --bmc1_ucm_layered_model                none
% 23.66/3.50  --bmc1_ucm_max_lemma_size               10
% 23.66/3.50  
% 23.66/3.50  ------ AIG Options
% 23.66/3.50  
% 23.66/3.50  --aig_mode                              false
% 23.66/3.50  
% 23.66/3.50  ------ Instantiation Options
% 23.66/3.50  
% 23.66/3.50  --instantiation_flag                    true
% 23.66/3.50  --inst_sos_flag                         false
% 23.66/3.50  --inst_sos_phase                        true
% 23.66/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.50  --inst_lit_sel_side                     none
% 23.66/3.50  --inst_solver_per_active                1400
% 23.66/3.50  --inst_solver_calls_frac                1.
% 23.66/3.50  --inst_passive_queue_type               priority_queues
% 23.66/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.50  --inst_passive_queues_freq              [25;2]
% 23.66/3.50  --inst_dismatching                      true
% 23.66/3.50  --inst_eager_unprocessed_to_passive     true
% 23.66/3.50  --inst_prop_sim_given                   true
% 23.66/3.50  --inst_prop_sim_new                     false
% 23.66/3.50  --inst_subs_new                         false
% 23.66/3.50  --inst_eq_res_simp                      false
% 23.66/3.50  --inst_subs_given                       false
% 23.66/3.50  --inst_orphan_elimination               true
% 23.66/3.50  --inst_learning_loop_flag               true
% 23.66/3.50  --inst_learning_start                   3000
% 23.66/3.50  --inst_learning_factor                  2
% 23.66/3.50  --inst_start_prop_sim_after_learn       3
% 23.66/3.50  --inst_sel_renew                        solver
% 23.66/3.50  --inst_lit_activity_flag                true
% 23.66/3.50  --inst_restr_to_given                   false
% 23.66/3.50  --inst_activity_threshold               500
% 23.66/3.50  --inst_out_proof                        true
% 23.66/3.50  
% 23.66/3.50  ------ Resolution Options
% 23.66/3.50  
% 23.66/3.50  --resolution_flag                       false
% 23.66/3.50  --res_lit_sel                           adaptive
% 23.66/3.50  --res_lit_sel_side                      none
% 23.66/3.50  --res_ordering                          kbo
% 23.66/3.50  --res_to_prop_solver                    active
% 23.66/3.50  --res_prop_simpl_new                    false
% 23.66/3.50  --res_prop_simpl_given                  true
% 23.66/3.50  --res_passive_queue_type                priority_queues
% 23.66/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.50  --res_passive_queues_freq               [15;5]
% 23.66/3.50  --res_forward_subs                      full
% 23.66/3.50  --res_backward_subs                     full
% 23.66/3.50  --res_forward_subs_resolution           true
% 23.66/3.50  --res_backward_subs_resolution          true
% 23.66/3.50  --res_orphan_elimination                true
% 23.66/3.50  --res_time_limit                        2.
% 23.66/3.50  --res_out_proof                         true
% 23.66/3.50  
% 23.66/3.50  ------ Superposition Options
% 23.66/3.50  
% 23.66/3.50  --superposition_flag                    true
% 23.66/3.50  --sup_passive_queue_type                priority_queues
% 23.66/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.50  --demod_completeness_check              fast
% 23.66/3.50  --demod_use_ground                      true
% 23.66/3.50  --sup_to_prop_solver                    passive
% 23.66/3.50  --sup_prop_simpl_new                    true
% 23.66/3.50  --sup_prop_simpl_given                  true
% 23.66/3.50  --sup_fun_splitting                     false
% 23.66/3.50  --sup_smt_interval                      50000
% 23.66/3.50  
% 23.66/3.50  ------ Superposition Simplification Setup
% 23.66/3.50  
% 23.66/3.50  --sup_indices_passive                   []
% 23.66/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.66/3.50  --sup_full_bw                           [BwDemod]
% 23.66/3.50  --sup_immed_triv                        [TrivRules]
% 23.66/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.66/3.50  --sup_immed_bw_main                     []
% 23.66/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.66/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.66/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.66/3.50  
% 23.66/3.50  ------ Combination Options
% 23.66/3.50  
% 23.66/3.50  --comb_res_mult                         3
% 23.66/3.50  --comb_sup_mult                         2
% 23.66/3.50  --comb_inst_mult                        10
% 23.66/3.50  
% 23.66/3.50  ------ Debug Options
% 23.66/3.50  
% 23.66/3.50  --dbg_backtrace                         false
% 23.66/3.50  --dbg_dump_prop_clauses                 false
% 23.66/3.50  --dbg_dump_prop_clauses_file            -
% 23.66/3.50  --dbg_out_stat                          false
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  ------ Proving...
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  % SZS status Theorem for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  fof(f10,axiom,(
% 23.66/3.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f24,plain,(
% 23.66/3.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 23.66/3.50    inference(ennf_transformation,[],[f10])).
% 23.66/3.50  
% 23.66/3.50  fof(f28,plain,(
% 23.66/3.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.66/3.50    inference(nnf_transformation,[],[f24])).
% 23.66/3.50  
% 23.66/3.50  fof(f29,plain,(
% 23.66/3.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.66/3.50    inference(flattening,[],[f28])).
% 23.66/3.50  
% 23.66/3.50  fof(f30,plain,(
% 23.66/3.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.66/3.50    inference(rectify,[],[f29])).
% 23.66/3.50  
% 23.66/3.50  fof(f31,plain,(
% 23.66/3.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f32,plain,(
% 23.66/3.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 23.66/3.50  
% 23.66/3.50  fof(f51,plain,(
% 23.66/3.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.66/3.50    inference(cnf_transformation,[],[f32])).
% 23.66/3.50  
% 23.66/3.50  fof(f15,axiom,(
% 23.66/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f65,plain,(
% 23.66/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f15])).
% 23.66/3.50  
% 23.66/3.50  fof(f16,axiom,(
% 23.66/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f66,plain,(
% 23.66/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f16])).
% 23.66/3.50  
% 23.66/3.50  fof(f17,axiom,(
% 23.66/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f67,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f17])).
% 23.66/3.50  
% 23.66/3.50  fof(f18,axiom,(
% 23.66/3.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f68,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f18])).
% 23.66/3.50  
% 23.66/3.50  fof(f19,axiom,(
% 23.66/3.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f69,plain,(
% 23.66/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f19])).
% 23.66/3.50  
% 23.66/3.50  fof(f74,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f68,f69])).
% 23.66/3.50  
% 23.66/3.50  fof(f75,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f67,f74])).
% 23.66/3.50  
% 23.66/3.50  fof(f76,plain,(
% 23.66/3.50    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f66,f75])).
% 23.66/3.50  
% 23.66/3.50  fof(f77,plain,(
% 23.66/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f65,f76])).
% 23.66/3.50  
% 23.66/3.50  fof(f87,plain,(
% 23.66/3.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 23.66/3.50    inference(definition_unfolding,[],[f51,f77])).
% 23.66/3.50  
% 23.66/3.50  fof(f102,plain,(
% 23.66/3.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 23.66/3.50    inference(equality_resolution,[],[f87])).
% 23.66/3.50  
% 23.66/3.50  fof(f103,plain,(
% 23.66/3.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 23.66/3.50    inference(equality_resolution,[],[f102])).
% 23.66/3.50  
% 23.66/3.50  fof(f21,conjecture,(
% 23.66/3.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k1_tarski(X2) = k2_tarski(X0,X1))),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f22,negated_conjecture,(
% 23.66/3.50    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k1_tarski(X2) = k2_tarski(X0,X1))),
% 23.66/3.50    inference(negated_conjecture,[],[f21])).
% 23.66/3.50  
% 23.66/3.50  fof(f25,plain,(
% 23.66/3.50    ? [X0,X1,X2] : (k1_tarski(X2) != k2_tarski(X0,X1) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 23.66/3.50    inference(ennf_transformation,[],[f22])).
% 23.66/3.50  
% 23.66/3.50  fof(f37,plain,(
% 23.66/3.50    ? [X0,X1,X2] : (k1_tarski(X2) != k2_tarski(X0,X1) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k1_tarski(sK4) != k2_tarski(sK2,sK3) & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f38,plain,(
% 23.66/3.50    k1_tarski(sK4) != k2_tarski(sK2,sK3) & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f37])).
% 23.66/3.50  
% 23.66/3.50  fof(f71,plain,(
% 23.66/3.50    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 23.66/3.50    inference(cnf_transformation,[],[f38])).
% 23.66/3.50  
% 23.66/3.50  fof(f13,axiom,(
% 23.66/3.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f63,plain,(
% 23.66/3.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f13])).
% 23.66/3.50  
% 23.66/3.50  fof(f14,axiom,(
% 23.66/3.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f64,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f14])).
% 23.66/3.50  
% 23.66/3.50  fof(f78,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f64,f77])).
% 23.66/3.50  
% 23.66/3.50  fof(f79,plain,(
% 23.66/3.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f63,f78])).
% 23.66/3.50  
% 23.66/3.50  fof(f95,plain,(
% 23.66/3.50    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 23.66/3.50    inference(definition_unfolding,[],[f71,f78,f79])).
% 23.66/3.50  
% 23.66/3.50  fof(f5,axiom,(
% 23.66/3.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f23,plain,(
% 23.66/3.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.66/3.50    inference(ennf_transformation,[],[f5])).
% 23.66/3.50  
% 23.66/3.50  fof(f45,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f23])).
% 23.66/3.50  
% 23.66/3.50  fof(f1,axiom,(
% 23.66/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f39,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f1])).
% 23.66/3.50  
% 23.66/3.50  fof(f12,axiom,(
% 23.66/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f62,plain,(
% 23.66/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f12])).
% 23.66/3.50  
% 23.66/3.50  fof(f9,axiom,(
% 23.66/3.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f49,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f9])).
% 23.66/3.50  
% 23.66/3.50  fof(f4,axiom,(
% 23.66/3.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f44,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f4])).
% 23.66/3.50  
% 23.66/3.50  fof(f73,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f49,f44])).
% 23.66/3.50  
% 23.66/3.50  fof(f80,plain,(
% 23.66/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f62,f73,f69,f79])).
% 23.66/3.50  
% 23.66/3.50  fof(f7,axiom,(
% 23.66/3.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f47,plain,(
% 23.66/3.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f7])).
% 23.66/3.50  
% 23.66/3.50  fof(f2,axiom,(
% 23.66/3.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f40,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f2])).
% 23.66/3.50  
% 23.66/3.50  fof(f8,axiom,(
% 23.66/3.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f48,plain,(
% 23.66/3.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 23.66/3.50    inference(cnf_transformation,[],[f8])).
% 23.66/3.50  
% 23.66/3.50  fof(f6,axiom,(
% 23.66/3.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f46,plain,(
% 23.66/3.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.66/3.50    inference(cnf_transformation,[],[f6])).
% 23.66/3.50  
% 23.66/3.50  fof(f11,axiom,(
% 23.66/3.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f33,plain,(
% 23.66/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 23.66/3.50    inference(nnf_transformation,[],[f11])).
% 23.66/3.50  
% 23.66/3.50  fof(f34,plain,(
% 23.66/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.66/3.50    inference(rectify,[],[f33])).
% 23.66/3.50  
% 23.66/3.50  fof(f35,plain,(
% 23.66/3.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f36,plain,(
% 23.66/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 23.66/3.50  
% 23.66/3.50  fof(f58,plain,(
% 23.66/3.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 23.66/3.50    inference(cnf_transformation,[],[f36])).
% 23.66/3.50  
% 23.66/3.50  fof(f92,plain,(
% 23.66/3.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 23.66/3.50    inference(definition_unfolding,[],[f58,f79])).
% 23.66/3.50  
% 23.66/3.50  fof(f107,plain,(
% 23.66/3.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 23.66/3.50    inference(equality_resolution,[],[f92])).
% 23.66/3.50  
% 23.66/3.50  fof(f20,axiom,(
% 23.66/3.50    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f70,plain,(
% 23.66/3.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 23.66/3.50    inference(cnf_transformation,[],[f20])).
% 23.66/3.50  
% 23.66/3.50  fof(f93,plain,(
% 23.66/3.50    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 23.66/3.50    inference(definition_unfolding,[],[f70,f79,f78])).
% 23.66/3.50  
% 23.66/3.50  fof(f3,axiom,(
% 23.66/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.66/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f26,plain,(
% 23.66/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.66/3.50    inference(nnf_transformation,[],[f3])).
% 23.66/3.50  
% 23.66/3.50  fof(f27,plain,(
% 23.66/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.66/3.50    inference(flattening,[],[f26])).
% 23.66/3.50  
% 23.66/3.50  fof(f43,plain,(
% 23.66/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f27])).
% 23.66/3.50  
% 23.66/3.50  fof(f72,plain,(
% 23.66/3.50    k1_tarski(sK4) != k2_tarski(sK2,sK3)),
% 23.66/3.50    inference(cnf_transformation,[],[f38])).
% 23.66/3.50  
% 23.66/3.50  fof(f94,plain,(
% 23.66/3.50    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 23.66/3.50    inference(definition_unfolding,[],[f72,f79,f78])).
% 23.66/3.50  
% 23.66/3.50  cnf(c_16,plain,
% 23.66/3.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1640,plain,
% 23.66/3.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_24,negated_conjecture,
% 23.66/3.50      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f95]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1633,plain,
% 23.66/3.50      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_6,plain,
% 23.66/3.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.66/3.50      inference(cnf_transformation,[],[f45]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1647,plain,
% 23.66/3.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_15163,plain,
% 23.66/3.50      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_1633,c_1647]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1,plain,
% 23.66/3.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.66/3.50      inference(cnf_transformation,[],[f39]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_0,plain,
% 23.66/3.50      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 23.66/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2126,plain,
% 23.66/3.50      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_60416,plain,
% 23.66/3.50      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_15163,c_2126]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_8,plain,
% 23.66/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2,plain,
% 23.66/3.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.66/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1756,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_8,c_2]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_9,plain,
% 23.66/3.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.66/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2051,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2048,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_7,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.66/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1888,plain,
% 23.66/3.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_7,c_2]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2058,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 23.66/3.50      inference(demodulation,[status(thm)],[c_2048,c_1888]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2314,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_2051,c_2058]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2332,plain,
% 23.66/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 23.66/3.50      inference(demodulation,[status(thm)],[c_2314,c_7]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2833,plain,
% 23.66/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_1756,c_2332]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_66172,plain,
% 23.66/3.50      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_60416,c_2833]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_66189,plain,
% 23.66/3.50      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 23.66/3.50      inference(demodulation,[status(thm)],[c_66172,c_9,c_1888]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_21,plain,
% 23.66/3.50      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 23.66/3.50      inference(cnf_transformation,[],[f107]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1635,plain,
% 23.66/3.50      ( X0 = X1
% 23.66/3.50      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_66936,plain,
% 23.66/3.50      ( sK4 = X0
% 23.66/3.50      | r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK4)) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_66189,c_1635]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_95631,plain,
% 23.66/3.50      ( sK4 = sK2 ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_1640,c_66936]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1355,plain,
% 23.66/3.50      ( X0 != X1
% 23.66/3.50      | X2 != X3
% 23.66/3.50      | X4 != X5
% 23.66/3.50      | X6 != X7
% 23.66/3.50      | X8 != X9
% 23.66/3.50      | X10 != X11
% 23.66/3.50      | X12 != X13
% 23.66/3.50      | X14 != X15
% 23.66/3.50      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 23.66/3.50      theory(equality) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2078,plain,
% 23.66/3.50      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
% 23.66/3.50      | sK4 != X0
% 23.66/3.50      | sK4 != X1
% 23.66/3.50      | sK4 != X2
% 23.66/3.50      | sK4 != X3
% 23.66/3.50      | sK4 != X4
% 23.66/3.50      | sK4 != X5
% 23.66/3.50      | sK4 != X6
% 23.66/3.50      | sK4 != X7 ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_1355]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_21168,plain,
% 23.66/3.50      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 23.66/3.50      | sK4 != sK2 ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_2078]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1358,plain,
% 23.66/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.66/3.50      theory(equality) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1823,plain,
% 23.66/3.50      ( ~ r1_tarski(X0,X1)
% 23.66/3.50      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 23.66/3.50      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != X1 ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_1358]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2077,plain,
% 23.66/3.50      ( ~ r1_tarski(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8)
% 23.66/3.50      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
% 23.66/3.50      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != X8 ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_1823]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_3420,plain,
% 23.66/3.50      ( ~ r1_tarski(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
% 23.66/3.50      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_2077]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_9183,plain,
% 23.66/3.50      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 23.66/3.50      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_3420]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_22,plain,
% 23.66/3.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_3746,plain,
% 23.66/3.50      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_22]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1353,plain,( X0 = X0 ),theory(equality) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1881,plain,
% 23.66/3.50      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_1353]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_3,plain,
% 23.66/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.66/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1779,plain,
% 23.66/3.50      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.66/3.50      | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 23.66/3.50      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_23,negated_conjecture,
% 23.66/3.50      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 23.66/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(contradiction,plain,
% 23.66/3.50      ( $false ),
% 23.66/3.50      inference(minisat,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_95631,c_21168,c_9183,c_3746,c_1881,c_1779,c_23,c_24]) ).
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  ------                               Statistics
% 23.66/3.50  
% 23.66/3.50  ------ General
% 23.66/3.50  
% 23.66/3.50  abstr_ref_over_cycles:                  0
% 23.66/3.50  abstr_ref_under_cycles:                 0
% 23.66/3.50  gc_basic_clause_elim:                   0
% 23.66/3.50  forced_gc_time:                         0
% 23.66/3.50  parsing_time:                           0.018
% 23.66/3.50  unif_index_cands_time:                  0.
% 23.66/3.50  unif_index_add_time:                    0.
% 23.66/3.50  orderings_time:                         0.
% 23.66/3.50  out_proof_time:                         0.01
% 23.66/3.50  total_time:                             2.922
% 23.66/3.50  num_of_symbols:                         42
% 23.66/3.50  num_of_terms:                           125441
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing
% 23.66/3.50  
% 23.66/3.50  num_of_splits:                          0
% 23.66/3.50  num_of_split_atoms:                     0
% 23.66/3.50  num_of_reused_defs:                     0
% 23.66/3.50  num_eq_ax_congr_red:                    18
% 23.66/3.50  num_of_sem_filtered_clauses:            1
% 23.66/3.50  num_of_subtypes:                        0
% 23.66/3.50  monotx_restored_types:                  0
% 23.66/3.50  sat_num_of_epr_types:                   0
% 23.66/3.50  sat_num_of_non_cyclic_types:            0
% 23.66/3.50  sat_guarded_non_collapsed_types:        0
% 23.66/3.50  num_pure_diseq_elim:                    0
% 23.66/3.50  simp_replaced_by:                       0
% 23.66/3.50  res_preprocessed:                       111
% 23.66/3.50  prep_upred:                             0
% 23.66/3.50  prep_unflattend:                        72
% 23.66/3.50  smt_new_axioms:                         0
% 23.66/3.50  pred_elim_cands:                        2
% 23.66/3.50  pred_elim:                              0
% 23.66/3.50  pred_elim_cl:                           0
% 23.66/3.50  pred_elim_cycles:                       2
% 23.66/3.50  merged_defs:                            0
% 23.66/3.50  merged_defs_ncl:                        0
% 23.66/3.50  bin_hyper_res:                          0
% 23.66/3.50  prep_cycles:                            4
% 23.66/3.50  pred_elim_time:                         0.012
% 23.66/3.50  splitting_time:                         0.
% 23.66/3.50  sem_filter_time:                        0.
% 23.66/3.50  monotx_time:                            0.
% 23.66/3.50  subtype_inf_time:                       0.
% 23.66/3.50  
% 23.66/3.50  ------ Problem properties
% 23.66/3.50  
% 23.66/3.50  clauses:                                24
% 23.66/3.50  conjectures:                            2
% 23.66/3.50  epr:                                    2
% 23.66/3.50  horn:                                   21
% 23.66/3.50  ground:                                 2
% 23.66/3.50  unary:                                  14
% 23.66/3.50  binary:                                 2
% 23.66/3.50  lits:                                   45
% 23.66/3.50  lits_eq:                                27
% 23.66/3.50  fd_pure:                                0
% 23.66/3.50  fd_pseudo:                              0
% 23.66/3.50  fd_cond:                                0
% 23.66/3.50  fd_pseudo_cond:                         7
% 23.66/3.50  ac_symbols:                             1
% 23.66/3.50  
% 23.66/3.50  ------ Propositional Solver
% 23.66/3.50  
% 23.66/3.50  prop_solver_calls:                      28
% 23.66/3.50  prop_fast_solver_calls:                 908
% 23.66/3.50  smt_solver_calls:                       0
% 23.66/3.50  smt_fast_solver_calls:                  0
% 23.66/3.50  prop_num_of_clauses:                    15629
% 23.66/3.50  prop_preprocess_simplified:             20839
% 23.66/3.50  prop_fo_subsumed:                       1
% 23.66/3.50  prop_solver_time:                       0.
% 23.66/3.50  smt_solver_time:                        0.
% 23.66/3.50  smt_fast_solver_time:                   0.
% 23.66/3.50  prop_fast_solver_time:                  0.
% 23.66/3.50  prop_unsat_core_time:                   0.001
% 23.66/3.50  
% 23.66/3.50  ------ QBF
% 23.66/3.50  
% 23.66/3.50  qbf_q_res:                              0
% 23.66/3.50  qbf_num_tautologies:                    0
% 23.66/3.50  qbf_prep_cycles:                        0
% 23.66/3.50  
% 23.66/3.50  ------ BMC1
% 23.66/3.50  
% 23.66/3.50  bmc1_current_bound:                     -1
% 23.66/3.50  bmc1_last_solved_bound:                 -1
% 23.66/3.50  bmc1_unsat_core_size:                   -1
% 23.66/3.50  bmc1_unsat_core_parents_size:           -1
% 23.66/3.50  bmc1_merge_next_fun:                    0
% 23.66/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.66/3.50  
% 23.66/3.50  ------ Instantiation
% 23.66/3.50  
% 23.66/3.50  inst_num_of_clauses:                    2204
% 23.66/3.50  inst_num_in_passive:                    715
% 23.66/3.50  inst_num_in_active:                     567
% 23.66/3.50  inst_num_in_unprocessed:                923
% 23.66/3.50  inst_num_of_loops:                      720
% 23.66/3.50  inst_num_of_learning_restarts:          0
% 23.66/3.50  inst_num_moves_active_passive:          152
% 23.66/3.50  inst_lit_activity:                      0
% 23.66/3.50  inst_lit_activity_moves:                0
% 23.66/3.50  inst_num_tautologies:                   0
% 23.66/3.50  inst_num_prop_implied:                  0
% 23.66/3.50  inst_num_existing_simplified:           0
% 23.66/3.50  inst_num_eq_res_simplified:             0
% 23.66/3.50  inst_num_child_elim:                    0
% 23.66/3.50  inst_num_of_dismatching_blockings:      2287
% 23.66/3.50  inst_num_of_non_proper_insts:           2921
% 23.66/3.50  inst_num_of_duplicates:                 0
% 23.66/3.50  inst_inst_num_from_inst_to_res:         0
% 23.66/3.50  inst_dismatching_checking_time:         0.
% 23.66/3.50  
% 23.66/3.50  ------ Resolution
% 23.66/3.50  
% 23.66/3.50  res_num_of_clauses:                     0
% 23.66/3.50  res_num_in_passive:                     0
% 23.66/3.50  res_num_in_active:                      0
% 23.66/3.50  res_num_of_loops:                       115
% 23.66/3.50  res_forward_subset_subsumed:            370
% 23.66/3.50  res_backward_subset_subsumed:           2
% 23.66/3.50  res_forward_subsumed:                   2
% 23.66/3.50  res_backward_subsumed:                  0
% 23.66/3.50  res_forward_subsumption_resolution:     0
% 23.66/3.50  res_backward_subsumption_resolution:    0
% 23.66/3.50  res_clause_to_clause_subsumption:       493087
% 23.66/3.50  res_orphan_elimination:                 0
% 23.66/3.50  res_tautology_del:                      99
% 23.66/3.50  res_num_eq_res_simplified:              0
% 23.66/3.50  res_num_sel_changes:                    0
% 23.66/3.50  res_moves_from_active_to_pass:          0
% 23.66/3.50  
% 23.66/3.50  ------ Superposition
% 23.66/3.50  
% 23.66/3.50  sup_time_total:                         0.
% 23.66/3.50  sup_time_generating:                    0.
% 23.66/3.50  sup_time_sim_full:                      0.
% 23.66/3.50  sup_time_sim_immed:                     0.
% 23.66/3.50  
% 23.66/3.50  sup_num_of_clauses:                     6954
% 23.66/3.50  sup_num_in_active:                      128
% 23.66/3.50  sup_num_in_passive:                     6826
% 23.66/3.50  sup_num_of_loops:                       142
% 23.66/3.50  sup_fw_superposition:                   18426
% 23.66/3.50  sup_bw_superposition:                   14871
% 23.66/3.50  sup_immediate_simplified:               14059
% 23.66/3.50  sup_given_eliminated:                   7
% 23.66/3.50  comparisons_done:                       0
% 23.66/3.50  comparisons_avoided:                    8
% 23.66/3.50  
% 23.66/3.50  ------ Simplifications
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  sim_fw_subset_subsumed:                 1
% 23.66/3.50  sim_bw_subset_subsumed:                 0
% 23.66/3.50  sim_fw_subsumed:                        1077
% 23.66/3.50  sim_bw_subsumed:                        26
% 23.66/3.50  sim_fw_subsumption_res:                 0
% 23.66/3.50  sim_bw_subsumption_res:                 0
% 23.66/3.50  sim_tautology_del:                      0
% 23.66/3.50  sim_eq_tautology_del:                   2343
% 23.66/3.50  sim_eq_res_simp:                        0
% 23.66/3.50  sim_fw_demodulated:                     7958
% 23.66/3.50  sim_bw_demodulated:                     1126
% 23.66/3.50  sim_light_normalised:                   5409
% 23.66/3.50  sim_joinable_taut:                      821
% 23.66/3.50  sim_joinable_simp:                      0
% 23.66/3.50  sim_ac_normalised:                      0
% 23.66/3.50  sim_smt_subsumption:                    0
% 23.66/3.50  
%------------------------------------------------------------------------------
