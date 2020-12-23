%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:32 EST 2020

% Result     : Theorem 15.34s
% Output     : CNFRefutation 15.34s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 277 expanded)
%              Number of clauses        :   32 (  38 expanded)
%              Number of leaves         :   17 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  262 ( 738 expanded)
%              Number of equality atoms :  135 ( 388 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK3,sK5) != k1_tarski(sK6)
      & r2_hidden(sK6,sK3)
      & k3_xboole_0(sK4,sK5) = k1_tarski(sK6)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k3_xboole_0(sK3,sK5) != k1_tarski(sK6)
    & r2_hidden(sK6,sK3)
    & k3_xboole_0(sK4,sK5) = k1_tarski(sK6)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f37])).

fof(f72,plain,(
    r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f71,plain,(
    k3_xboole_0(sK4,sK5) = k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f103,plain,(
    k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f71,f48,f79])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f116,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f70,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f46,f48,f48,f48,f48])).

fof(f73,plain,(
    k3_xboole_0(sK3,sK5) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f73,f48,f79])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35038,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35046,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,negated_conjecture,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_35041,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_37451,plain,
    ( sK6 = X0
    | r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_35041])).

cnf(c_38366,plain,
    ( sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),X1) = sK6
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = X1
    | r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_35046,c_37451])).

cnf(c_39737,plain,
    ( sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) = sK6
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_38366,c_37451])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35047,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_40864,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_39737,c_35047])).

cnf(c_36233,plain,
    ( r2_hidden(sK0(X0,X1,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),X1)
    | r2_hidden(sK0(X0,X1,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_38233,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_36233])).

cnf(c_40704,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_38233])).

cnf(c_40705,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40704])).

cnf(c_48245,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40864,c_40705])).

cnf(c_48254,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_35038,c_48245])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35037,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_35044,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_35332,plain,
    ( k2_xboole_0(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_35037,c_35044])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35466,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_35332,c_8])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35623,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_35466,c_7])).

cnf(c_48276,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_48254,c_35623])).

cnf(c_23,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3343,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_23,c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48276,c_3343])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.34/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.34/2.50  
% 15.34/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.34/2.50  
% 15.34/2.50  ------  iProver source info
% 15.34/2.50  
% 15.34/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.34/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.34/2.50  git: non_committed_changes: false
% 15.34/2.50  git: last_make_outside_of_git: false
% 15.34/2.50  
% 15.34/2.50  ------ 
% 15.34/2.50  ------ Parsing...
% 15.34/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  ------ Proving...
% 15.34/2.50  ------ Problem Properties 
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  clauses                                 27
% 15.34/2.50  conjectures                             4
% 15.34/2.50  EPR                                     2
% 15.34/2.50  Horn                                    22
% 15.34/2.50  unary                                   10
% 15.34/2.50  binary                                  6
% 15.34/2.50  lits                                    59
% 15.34/2.50  lits eq                                 26
% 15.34/2.50  fd_pure                                 0
% 15.34/2.50  fd_pseudo                               0
% 15.34/2.50  fd_cond                                 0
% 15.34/2.50  fd_pseudo_cond                          9
% 15.34/2.50  AC symbols                              0
% 15.34/2.50  
% 15.34/2.50  ------ Input Options Time Limit: Unbounded
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing...
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.34/2.50  Current options:
% 15.34/2.50  ------ 
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.34/2.50  
% 15.34/2.50  ------ Proving...
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  % SZS status Theorem for theBenchmark.p
% 15.34/2.50  
% 15.34/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.34/2.50  
% 15.34/2.50  fof(f16,conjecture,(
% 15.34/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f17,negated_conjecture,(
% 15.34/2.50    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 15.34/2.50    inference(negated_conjecture,[],[f16])).
% 15.34/2.50  
% 15.34/2.50  fof(f20,plain,(
% 15.34/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 15.34/2.50    inference(ennf_transformation,[],[f17])).
% 15.34/2.50  
% 15.34/2.50  fof(f21,plain,(
% 15.34/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 15.34/2.50    inference(flattening,[],[f20])).
% 15.34/2.50  
% 15.34/2.50  fof(f37,plain,(
% 15.34/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK3,sK5) != k1_tarski(sK6) & r2_hidden(sK6,sK3) & k3_xboole_0(sK4,sK5) = k1_tarski(sK6) & r1_tarski(sK3,sK4))),
% 15.34/2.50    introduced(choice_axiom,[])).
% 15.34/2.50  
% 15.34/2.50  fof(f38,plain,(
% 15.34/2.50    k3_xboole_0(sK3,sK5) != k1_tarski(sK6) & r2_hidden(sK6,sK3) & k3_xboole_0(sK4,sK5) = k1_tarski(sK6) & r1_tarski(sK3,sK4)),
% 15.34/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f37])).
% 15.34/2.50  
% 15.34/2.50  fof(f72,plain,(
% 15.34/2.50    r2_hidden(sK6,sK3)),
% 15.34/2.50    inference(cnf_transformation,[],[f38])).
% 15.34/2.50  
% 15.34/2.50  fof(f1,axiom,(
% 15.34/2.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f22,plain,(
% 15.34/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.34/2.50    inference(nnf_transformation,[],[f1])).
% 15.34/2.50  
% 15.34/2.50  fof(f23,plain,(
% 15.34/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.34/2.50    inference(flattening,[],[f22])).
% 15.34/2.50  
% 15.34/2.50  fof(f24,plain,(
% 15.34/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.34/2.50    inference(rectify,[],[f23])).
% 15.34/2.50  
% 15.34/2.50  fof(f25,plain,(
% 15.34/2.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.34/2.50    introduced(choice_axiom,[])).
% 15.34/2.50  
% 15.34/2.50  fof(f26,plain,(
% 15.34/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.34/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 15.34/2.50  
% 15.34/2.50  fof(f43,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f26])).
% 15.34/2.50  
% 15.34/2.50  fof(f5,axiom,(
% 15.34/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f48,plain,(
% 15.34/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.34/2.50    inference(cnf_transformation,[],[f5])).
% 15.34/2.50  
% 15.34/2.50  fof(f81,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f43,f48])).
% 15.34/2.50  
% 15.34/2.50  fof(f71,plain,(
% 15.34/2.50    k3_xboole_0(sK4,sK5) = k1_tarski(sK6)),
% 15.34/2.50    inference(cnf_transformation,[],[f38])).
% 15.34/2.50  
% 15.34/2.50  fof(f8,axiom,(
% 15.34/2.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f61,plain,(
% 15.34/2.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f8])).
% 15.34/2.50  
% 15.34/2.50  fof(f9,axiom,(
% 15.34/2.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f62,plain,(
% 15.34/2.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f9])).
% 15.34/2.50  
% 15.34/2.50  fof(f10,axiom,(
% 15.34/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f63,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f10])).
% 15.34/2.50  
% 15.34/2.50  fof(f11,axiom,(
% 15.34/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f64,plain,(
% 15.34/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f11])).
% 15.34/2.50  
% 15.34/2.50  fof(f12,axiom,(
% 15.34/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f65,plain,(
% 15.34/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f12])).
% 15.34/2.50  
% 15.34/2.50  fof(f13,axiom,(
% 15.34/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f66,plain,(
% 15.34/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f13])).
% 15.34/2.50  
% 15.34/2.50  fof(f14,axiom,(
% 15.34/2.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f67,plain,(
% 15.34/2.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f14])).
% 15.34/2.50  
% 15.34/2.50  fof(f74,plain,(
% 15.34/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f66,f67])).
% 15.34/2.50  
% 15.34/2.50  fof(f75,plain,(
% 15.34/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f65,f74])).
% 15.34/2.50  
% 15.34/2.50  fof(f76,plain,(
% 15.34/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f64,f75])).
% 15.34/2.50  
% 15.34/2.50  fof(f77,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f63,f76])).
% 15.34/2.50  
% 15.34/2.50  fof(f78,plain,(
% 15.34/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f62,f77])).
% 15.34/2.50  
% 15.34/2.50  fof(f79,plain,(
% 15.34/2.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f61,f78])).
% 15.34/2.50  
% 15.34/2.50  fof(f103,plain,(
% 15.34/2.50    k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),
% 15.34/2.50    inference(definition_unfolding,[],[f71,f48,f79])).
% 15.34/2.50  
% 15.34/2.50  fof(f7,axiom,(
% 15.34/2.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f32,plain,(
% 15.34/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 15.34/2.50    inference(nnf_transformation,[],[f7])).
% 15.34/2.50  
% 15.34/2.50  fof(f33,plain,(
% 15.34/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.34/2.50    inference(rectify,[],[f32])).
% 15.34/2.50  
% 15.34/2.50  fof(f34,plain,(
% 15.34/2.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 15.34/2.50    introduced(choice_axiom,[])).
% 15.34/2.50  
% 15.34/2.50  fof(f35,plain,(
% 15.34/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.34/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 15.34/2.50  
% 15.34/2.50  fof(f57,plain,(
% 15.34/2.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 15.34/2.50    inference(cnf_transformation,[],[f35])).
% 15.34/2.50  
% 15.34/2.50  fof(f99,plain,(
% 15.34/2.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 15.34/2.50    inference(definition_unfolding,[],[f57,f79])).
% 15.34/2.50  
% 15.34/2.50  fof(f116,plain,(
% 15.34/2.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 15.34/2.50    inference(equality_resolution,[],[f99])).
% 15.34/2.50  
% 15.34/2.50  fof(f44,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f26])).
% 15.34/2.50  
% 15.34/2.50  fof(f80,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.34/2.50    inference(definition_unfolding,[],[f44,f48])).
% 15.34/2.50  
% 15.34/2.50  fof(f70,plain,(
% 15.34/2.50    r1_tarski(sK3,sK4)),
% 15.34/2.50    inference(cnf_transformation,[],[f38])).
% 15.34/2.50  
% 15.34/2.50  fof(f2,axiom,(
% 15.34/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f18,plain,(
% 15.34/2.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.34/2.50    inference(ennf_transformation,[],[f2])).
% 15.34/2.50  
% 15.34/2.50  fof(f45,plain,(
% 15.34/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f18])).
% 15.34/2.50  
% 15.34/2.50  fof(f4,axiom,(
% 15.34/2.50    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f47,plain,(
% 15.34/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 15.34/2.50    inference(cnf_transformation,[],[f4])).
% 15.34/2.50  
% 15.34/2.50  fof(f87,plain,(
% 15.34/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 15.34/2.50    inference(definition_unfolding,[],[f47,f48])).
% 15.34/2.50  
% 15.34/2.50  fof(f3,axiom,(
% 15.34/2.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.34/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.34/2.50  
% 15.34/2.50  fof(f46,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.34/2.50    inference(cnf_transformation,[],[f3])).
% 15.34/2.50  
% 15.34/2.50  fof(f86,plain,(
% 15.34/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 15.34/2.50    inference(definition_unfolding,[],[f46,f48,f48,f48,f48])).
% 15.34/2.50  
% 15.34/2.50  fof(f73,plain,(
% 15.34/2.50    k3_xboole_0(sK3,sK5) != k1_tarski(sK6)),
% 15.34/2.50    inference(cnf_transformation,[],[f38])).
% 15.34/2.50  
% 15.34/2.50  fof(f102,plain,(
% 15.34/2.50    k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),
% 15.34/2.50    inference(definition_unfolding,[],[f73,f48,f79])).
% 15.34/2.50  
% 15.34/2.50  cnf(c_24,negated_conjecture,
% 15.34/2.50      ( r2_hidden(sK6,sK3) ),
% 15.34/2.50      inference(cnf_transformation,[],[f72]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35038,plain,
% 15.34/2.50      ( r2_hidden(sK6,sK3) = iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_1,plain,
% 15.34/2.50      ( r2_hidden(sK0(X0,X1,X2),X1)
% 15.34/2.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.34/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35046,plain,
% 15.34/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 15.34/2.50      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 15.34/2.50      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_25,negated_conjecture,
% 15.34/2.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 15.34/2.50      inference(cnf_transformation,[],[f103]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_20,plain,
% 15.34/2.50      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 15.34/2.50      inference(cnf_transformation,[],[f116]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35041,plain,
% 15.34/2.50      ( X0 = X1
% 15.34/2.50      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_37451,plain,
% 15.34/2.50      ( sK6 = X0
% 15.34/2.50      | r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) != iProver_top ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_25,c_35041]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_38366,plain,
% 15.34/2.50      ( sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),X1) = sK6
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = X1
% 15.34/2.50      | r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),X1),X1) = iProver_top ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_35046,c_37451]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_39737,plain,
% 15.34/2.50      ( sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) = sK6
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_38366,c_37451]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_0,plain,
% 15.34/2.50      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 15.34/2.50      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 15.34/2.50      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.34/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35047,plain,
% 15.34/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 15.34/2.50      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 15.34/2.50      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 15.34/2.50      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_40864,plain,
% 15.34/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 15.34/2.50      | r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) != iProver_top
% 15.34/2.50      | r2_hidden(sK6,X0) != iProver_top ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_39737,c_35047]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_36233,plain,
% 15.34/2.50      ( r2_hidden(sK0(X0,X1,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),X1)
% 15.34/2.50      | r2_hidden(sK0(X0,X1,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 15.34/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_38233,plain,
% 15.34/2.50      ( r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 15.34/2.50      | r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 15.34/2.50      inference(instantiation,[status(thm)],[c_36233]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_40704,plain,
% 15.34/2.50      ( r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 15.34/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 15.34/2.50      inference(instantiation,[status(thm)],[c_38233]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_40705,plain,
% 15.34/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 15.34/2.50      | r2_hidden(sK0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) = iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_40704]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_48245,plain,
% 15.34/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 15.34/2.50      | r2_hidden(sK6,X0) != iProver_top ),
% 15.34/2.50      inference(global_propositional_subsumption,
% 15.34/2.50                [status(thm)],
% 15.34/2.50                [c_40864,c_40705]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_48254,plain,
% 15.34/2.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_35038,c_48245]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_26,negated_conjecture,
% 15.34/2.50      ( r1_tarski(sK3,sK4) ),
% 15.34/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35037,plain,
% 15.34/2.50      ( r1_tarski(sK3,sK4) = iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_6,plain,
% 15.34/2.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.34/2.50      inference(cnf_transformation,[],[f45]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35044,plain,
% 15.34/2.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.34/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35332,plain,
% 15.34/2.50      ( k2_xboole_0(sK3,sK4) = sK4 ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_35037,c_35044]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_8,plain,
% 15.34/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 15.34/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35466,plain,
% 15.34/2.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = sK3 ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_35332,c_8]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_7,plain,
% 15.34/2.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 15.34/2.50      inference(cnf_transformation,[],[f86]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_35623,plain,
% 15.34/2.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 15.34/2.50      inference(superposition,[status(thm)],[c_35466,c_7]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_48276,plain,
% 15.34/2.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
% 15.34/2.50      inference(demodulation,[status(thm)],[c_48254,c_35623]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_23,negated_conjecture,
% 15.34/2.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 15.34/2.50      inference(cnf_transformation,[],[f102]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(c_3343,plain,
% 15.34/2.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) ),
% 15.34/2.50      inference(light_normalisation,[status(thm)],[c_23,c_25]) ).
% 15.34/2.50  
% 15.34/2.50  cnf(contradiction,plain,
% 15.34/2.50      ( $false ),
% 15.34/2.50      inference(minisat,[status(thm)],[c_48276,c_3343]) ).
% 15.34/2.50  
% 15.34/2.50  
% 15.34/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.34/2.50  
% 15.34/2.50  ------                               Statistics
% 15.34/2.50  
% 15.34/2.50  ------ Selected
% 15.34/2.50  
% 15.34/2.50  total_time:                             1.538
% 15.34/2.50  
%------------------------------------------------------------------------------
