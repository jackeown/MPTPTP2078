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
% DateTime   : Thu Dec  3 11:31:54 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 868 expanded)
%              Number of clauses        :   77 ( 302 expanded)
%              Number of leaves         :   13 ( 157 expanded)
%              Depth                    :   20
%              Number of atoms          :  411 (3059 expanded)
%              Number of equality atoms :  205 (1076 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | ~ r2_hidden(sK3,sK5)
        | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) )
      & ( ( r2_hidden(sK4,sK5)
          & r2_hidden(sK3,sK5) )
        | r1_tarski(k2_tarski(sK3,sK4),sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | ~ r2_hidden(sK3,sK5)
      | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) )
    & ( ( r2_hidden(sK4,sK5)
        & r2_hidden(sK3,sK5) )
      | r1_tarski(k2_tarski(sK3,sK4),sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f40])).

fof(f70,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f69,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f69,f63])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f79,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f78])).

fof(f68,plain,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1141,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1122,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1136,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1933,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1136])).

cnf(c_3953,plain,
    ( k2_xboole_0(k1_tarski(sK0(X0,X1)),X0) = X0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1933])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK4,sK5)
    | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1118,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6799,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK3,sK3,sK4),sK5)),k1_enumset1(sK3,sK3,sK4)) = k1_enumset1(sK3,sK3,sK4)
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3953,c_1118])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1173,plain,
    ( r2_hidden(sK3,sK5)
    | ~ r1_tarski(k1_tarski(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1174,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r1_tarski(k1_tarski(sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1138,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1117,plain,
    ( r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1633,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1136])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1140,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2720,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
    | r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1140])).

cnf(c_29,plain,
    ( r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1219,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1265,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(X0,X1,sK4))
    | r2_hidden(sK4,sK5)
    | ~ r1_tarski(k1_enumset1(X0,X1,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1266,plain,
    ( r2_hidden(sK4,k1_enumset1(X0,X1,sK4)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k1_enumset1(X0,X1,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_1268,plain,
    ( r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1262,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1368,plain,
    ( r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1369,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3057,plain,
    ( r2_hidden(sK4,k1_enumset1(X0,X1,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3058,plain,
    ( r2_hidden(sK4,k1_enumset1(X0,X1,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3057])).

cnf(c_3060,plain,
    ( r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3058])).

cnf(c_3116,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2720,c_29,c_1268,c_1369,c_3060])).

cnf(c_3122,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_3116])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1116,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1634,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1136])).

cnf(c_3962,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
    | k2_xboole_0(k1_tarski(sK3),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1634,c_1933])).

cnf(c_23,plain,
    ( r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1120,plain,
    ( r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1632,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1120,c_1136])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1137,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2122,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1137])).

cnf(c_2322,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1137])).

cnf(c_1121,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2547,plain,
    ( r2_hidden(X0,k2_xboole_0(k2_xboole_0(k1_tarski(X0),X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1121])).

cnf(c_2565,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_enumset1(X0,X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_2547])).

cnf(c_4226,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK5) = sK5
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_2565])).

cnf(c_30,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4224,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK5) = sK5
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_2122])).

cnf(c_4353,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4226,c_29,c_30,c_1268,c_3060,c_4224])).

cnf(c_4357,plain,
    ( r1_tarski(k1_tarski(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_2122])).

cnf(c_7184,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK3,sK3,sK4),sK5)),k1_enumset1(sK3,sK3,sK4)) = k1_enumset1(sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6799,c_29,c_1174,c_1268,c_3060,c_4357])).

cnf(c_2323,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1121])).

cnf(c_7195,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),k1_enumset1(sK3,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7184,c_2323])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1127,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7223,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK3
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_7195,c_1127])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1299,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1308,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1467,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1980,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_3017,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_584,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2100,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_3149,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2100])).

cnf(c_3150,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | sK5 != sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3149])).

cnf(c_3152,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) != sK3
    | sK5 != sK5
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3150])).

cnf(c_11405,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7223,c_29,c_30,c_1174,c_1268,c_1308,c_1980,c_3017,c_3060,c_3152,c_4357])).

cnf(c_1142,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11498,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_11405,c_1142])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11498,c_4357,c_3122,c_1174,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.00  
% 3.44/1.00  ------  iProver source info
% 3.44/1.00  
% 3.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.00  git: non_committed_changes: false
% 3.44/1.00  git: last_make_outside_of_git: false
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  
% 3.44/1.00  ------ Input Options
% 3.44/1.00  
% 3.44/1.00  --out_options                           all
% 3.44/1.00  --tptp_safe_out                         true
% 3.44/1.00  --problem_path                          ""
% 3.44/1.00  --include_path                          ""
% 3.44/1.00  --clausifier                            res/vclausify_rel
% 3.44/1.00  --clausifier_options                    ""
% 3.44/1.00  --stdin                                 false
% 3.44/1.00  --stats_out                             all
% 3.44/1.00  
% 3.44/1.00  ------ General Options
% 3.44/1.00  
% 3.44/1.00  --fof                                   false
% 3.44/1.00  --time_out_real                         305.
% 3.44/1.00  --time_out_virtual                      -1.
% 3.44/1.00  --symbol_type_check                     false
% 3.44/1.00  --clausify_out                          false
% 3.44/1.00  --sig_cnt_out                           false
% 3.44/1.00  --trig_cnt_out                          false
% 3.44/1.00  --trig_cnt_out_tolerance                1.
% 3.44/1.00  --trig_cnt_out_sk_spl                   false
% 3.44/1.00  --abstr_cl_out                          false
% 3.44/1.00  
% 3.44/1.00  ------ Global Options
% 3.44/1.00  
% 3.44/1.00  --schedule                              default
% 3.44/1.00  --add_important_lit                     false
% 3.44/1.00  --prop_solver_per_cl                    1000
% 3.44/1.00  --min_unsat_core                        false
% 3.44/1.00  --soft_assumptions                      false
% 3.44/1.00  --soft_lemma_size                       3
% 3.44/1.00  --prop_impl_unit_size                   0
% 3.44/1.00  --prop_impl_unit                        []
% 3.44/1.00  --share_sel_clauses                     true
% 3.44/1.00  --reset_solvers                         false
% 3.44/1.00  --bc_imp_inh                            [conj_cone]
% 3.44/1.00  --conj_cone_tolerance                   3.
% 3.44/1.00  --extra_neg_conj                        none
% 3.44/1.00  --large_theory_mode                     true
% 3.44/1.00  --prolific_symb_bound                   200
% 3.44/1.00  --lt_threshold                          2000
% 3.44/1.00  --clause_weak_htbl                      true
% 3.44/1.00  --gc_record_bc_elim                     false
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing Options
% 3.44/1.00  
% 3.44/1.00  --preprocessing_flag                    true
% 3.44/1.00  --time_out_prep_mult                    0.1
% 3.44/1.00  --splitting_mode                        input
% 3.44/1.00  --splitting_grd                         true
% 3.44/1.00  --splitting_cvd                         false
% 3.44/1.00  --splitting_cvd_svl                     false
% 3.44/1.00  --splitting_nvd                         32
% 3.44/1.00  --sub_typing                            true
% 3.44/1.00  --prep_gs_sim                           true
% 3.44/1.00  --prep_unflatten                        true
% 3.44/1.00  --prep_res_sim                          true
% 3.44/1.00  --prep_upred                            true
% 3.44/1.00  --prep_sem_filter                       exhaustive
% 3.44/1.00  --prep_sem_filter_out                   false
% 3.44/1.00  --pred_elim                             true
% 3.44/1.00  --res_sim_input                         true
% 3.44/1.00  --eq_ax_congr_red                       true
% 3.44/1.00  --pure_diseq_elim                       true
% 3.44/1.00  --brand_transform                       false
% 3.44/1.00  --non_eq_to_eq                          false
% 3.44/1.00  --prep_def_merge                        true
% 3.44/1.00  --prep_def_merge_prop_impl              false
% 3.44/1.00  --prep_def_merge_mbd                    true
% 3.44/1.00  --prep_def_merge_tr_red                 false
% 3.44/1.00  --prep_def_merge_tr_cl                  false
% 3.44/1.00  --smt_preprocessing                     true
% 3.44/1.00  --smt_ac_axioms                         fast
% 3.44/1.00  --preprocessed_out                      false
% 3.44/1.00  --preprocessed_stats                    false
% 3.44/1.00  
% 3.44/1.00  ------ Abstraction refinement Options
% 3.44/1.00  
% 3.44/1.00  --abstr_ref                             []
% 3.44/1.00  --abstr_ref_prep                        false
% 3.44/1.00  --abstr_ref_until_sat                   false
% 3.44/1.00  --abstr_ref_sig_restrict                funpre
% 3.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.00  --abstr_ref_under                       []
% 3.44/1.00  
% 3.44/1.00  ------ SAT Options
% 3.44/1.00  
% 3.44/1.00  --sat_mode                              false
% 3.44/1.00  --sat_fm_restart_options                ""
% 3.44/1.00  --sat_gr_def                            false
% 3.44/1.00  --sat_epr_types                         true
% 3.44/1.00  --sat_non_cyclic_types                  false
% 3.44/1.00  --sat_finite_models                     false
% 3.44/1.00  --sat_fm_lemmas                         false
% 3.44/1.00  --sat_fm_prep                           false
% 3.44/1.00  --sat_fm_uc_incr                        true
% 3.44/1.00  --sat_out_model                         small
% 3.44/1.00  --sat_out_clauses                       false
% 3.44/1.00  
% 3.44/1.00  ------ QBF Options
% 3.44/1.00  
% 3.44/1.00  --qbf_mode                              false
% 3.44/1.00  --qbf_elim_univ                         false
% 3.44/1.00  --qbf_dom_inst                          none
% 3.44/1.00  --qbf_dom_pre_inst                      false
% 3.44/1.00  --qbf_sk_in                             false
% 3.44/1.00  --qbf_pred_elim                         true
% 3.44/1.00  --qbf_split                             512
% 3.44/1.00  
% 3.44/1.00  ------ BMC1 Options
% 3.44/1.00  
% 3.44/1.00  --bmc1_incremental                      false
% 3.44/1.00  --bmc1_axioms                           reachable_all
% 3.44/1.00  --bmc1_min_bound                        0
% 3.44/1.00  --bmc1_max_bound                        -1
% 3.44/1.00  --bmc1_max_bound_default                -1
% 3.44/1.00  --bmc1_symbol_reachability              true
% 3.44/1.00  --bmc1_property_lemmas                  false
% 3.44/1.00  --bmc1_k_induction                      false
% 3.44/1.00  --bmc1_non_equiv_states                 false
% 3.44/1.00  --bmc1_deadlock                         false
% 3.44/1.00  --bmc1_ucm                              false
% 3.44/1.00  --bmc1_add_unsat_core                   none
% 3.44/1.00  --bmc1_unsat_core_children              false
% 3.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.00  --bmc1_out_stat                         full
% 3.44/1.00  --bmc1_ground_init                      false
% 3.44/1.00  --bmc1_pre_inst_next_state              false
% 3.44/1.00  --bmc1_pre_inst_state                   false
% 3.44/1.00  --bmc1_pre_inst_reach_state             false
% 3.44/1.00  --bmc1_out_unsat_core                   false
% 3.44/1.00  --bmc1_aig_witness_out                  false
% 3.44/1.00  --bmc1_verbose                          false
% 3.44/1.00  --bmc1_dump_clauses_tptp                false
% 3.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.00  --bmc1_dump_file                        -
% 3.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.00  --bmc1_ucm_extend_mode                  1
% 3.44/1.00  --bmc1_ucm_init_mode                    2
% 3.44/1.00  --bmc1_ucm_cone_mode                    none
% 3.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.00  --bmc1_ucm_relax_model                  4
% 3.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.00  --bmc1_ucm_layered_model                none
% 3.44/1.00  --bmc1_ucm_max_lemma_size               10
% 3.44/1.00  
% 3.44/1.00  ------ AIG Options
% 3.44/1.00  
% 3.44/1.00  --aig_mode                              false
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation Options
% 3.44/1.00  
% 3.44/1.00  --instantiation_flag                    true
% 3.44/1.00  --inst_sos_flag                         true
% 3.44/1.00  --inst_sos_phase                        true
% 3.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel_side                     num_symb
% 3.44/1.00  --inst_solver_per_active                1400
% 3.44/1.00  --inst_solver_calls_frac                1.
% 3.44/1.00  --inst_passive_queue_type               priority_queues
% 3.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.00  --inst_passive_queues_freq              [25;2]
% 3.44/1.00  --inst_dismatching                      true
% 3.44/1.00  --inst_eager_unprocessed_to_passive     true
% 3.44/1.00  --inst_prop_sim_given                   true
% 3.44/1.00  --inst_prop_sim_new                     false
% 3.44/1.00  --inst_subs_new                         false
% 3.44/1.00  --inst_eq_res_simp                      false
% 3.44/1.00  --inst_subs_given                       false
% 3.44/1.00  --inst_orphan_elimination               true
% 3.44/1.00  --inst_learning_loop_flag               true
% 3.44/1.00  --inst_learning_start                   3000
% 3.44/1.00  --inst_learning_factor                  2
% 3.44/1.00  --inst_start_prop_sim_after_learn       3
% 3.44/1.00  --inst_sel_renew                        solver
% 3.44/1.00  --inst_lit_activity_flag                true
% 3.44/1.00  --inst_restr_to_given                   false
% 3.44/1.00  --inst_activity_threshold               500
% 3.44/1.00  --inst_out_proof                        true
% 3.44/1.00  
% 3.44/1.00  ------ Resolution Options
% 3.44/1.00  
% 3.44/1.00  --resolution_flag                       true
% 3.44/1.00  --res_lit_sel                           adaptive
% 3.44/1.00  --res_lit_sel_side                      none
% 3.44/1.00  --res_ordering                          kbo
% 3.44/1.00  --res_to_prop_solver                    active
% 3.44/1.00  --res_prop_simpl_new                    false
% 3.44/1.00  --res_prop_simpl_given                  true
% 3.44/1.00  --res_passive_queue_type                priority_queues
% 3.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.00  --res_passive_queues_freq               [15;5]
% 3.44/1.00  --res_forward_subs                      full
% 3.44/1.00  --res_backward_subs                     full
% 3.44/1.00  --res_forward_subs_resolution           true
% 3.44/1.00  --res_backward_subs_resolution          true
% 3.44/1.00  --res_orphan_elimination                true
% 3.44/1.00  --res_time_limit                        2.
% 3.44/1.00  --res_out_proof                         true
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Options
% 3.44/1.00  
% 3.44/1.00  --superposition_flag                    true
% 3.44/1.00  --sup_passive_queue_type                priority_queues
% 3.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.00  --demod_completeness_check              fast
% 3.44/1.00  --demod_use_ground                      true
% 3.44/1.00  --sup_to_prop_solver                    passive
% 3.44/1.00  --sup_prop_simpl_new                    true
% 3.44/1.00  --sup_prop_simpl_given                  true
% 3.44/1.00  --sup_fun_splitting                     true
% 3.44/1.00  --sup_smt_interval                      50000
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Simplification Setup
% 3.44/1.00  
% 3.44/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.44/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.44/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.44/1.00  --sup_immed_triv                        [TrivRules]
% 3.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_immed_bw_main                     []
% 3.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_input_bw                          []
% 3.44/1.00  
% 3.44/1.00  ------ Combination Options
% 3.44/1.00  
% 3.44/1.00  --comb_res_mult                         3
% 3.44/1.00  --comb_sup_mult                         2
% 3.44/1.00  --comb_inst_mult                        10
% 3.44/1.00  
% 3.44/1.00  ------ Debug Options
% 3.44/1.00  
% 3.44/1.00  --dbg_backtrace                         false
% 3.44/1.00  --dbg_dump_prop_clauses                 false
% 3.44/1.00  --dbg_dump_prop_clauses_file            -
% 3.44/1.00  --dbg_out_stat                          false
% 3.44/1.00  ------ Parsing...
% 3.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/1.00  ------ Proving...
% 3.44/1.00  ------ Problem Properties 
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  clauses                                 27
% 3.44/1.00  conjectures                             3
% 3.44/1.00  EPR                                     4
% 3.44/1.00  Horn                                    20
% 3.44/1.00  unary                                   6
% 3.44/1.00  binary                                  9
% 3.44/1.00  lits                                    63
% 3.44/1.00  lits eq                                 22
% 3.44/1.00  fd_pure                                 0
% 3.44/1.00  fd_pseudo                               0
% 3.44/1.00  fd_cond                                 0
% 3.44/1.00  fd_pseudo_cond                          8
% 3.44/1.00  AC symbols                              0
% 3.44/1.00  
% 3.44/1.00  ------ Schedule dynamic 5 is on 
% 3.44/1.00  
% 3.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  Current options:
% 3.44/1.00  ------ 
% 3.44/1.00  
% 3.44/1.00  ------ Input Options
% 3.44/1.00  
% 3.44/1.00  --out_options                           all
% 3.44/1.00  --tptp_safe_out                         true
% 3.44/1.00  --problem_path                          ""
% 3.44/1.00  --include_path                          ""
% 3.44/1.00  --clausifier                            res/vclausify_rel
% 3.44/1.00  --clausifier_options                    ""
% 3.44/1.00  --stdin                                 false
% 3.44/1.00  --stats_out                             all
% 3.44/1.00  
% 3.44/1.00  ------ General Options
% 3.44/1.00  
% 3.44/1.00  --fof                                   false
% 3.44/1.00  --time_out_real                         305.
% 3.44/1.00  --time_out_virtual                      -1.
% 3.44/1.00  --symbol_type_check                     false
% 3.44/1.00  --clausify_out                          false
% 3.44/1.00  --sig_cnt_out                           false
% 3.44/1.00  --trig_cnt_out                          false
% 3.44/1.00  --trig_cnt_out_tolerance                1.
% 3.44/1.00  --trig_cnt_out_sk_spl                   false
% 3.44/1.00  --abstr_cl_out                          false
% 3.44/1.00  
% 3.44/1.00  ------ Global Options
% 3.44/1.00  
% 3.44/1.00  --schedule                              default
% 3.44/1.00  --add_important_lit                     false
% 3.44/1.00  --prop_solver_per_cl                    1000
% 3.44/1.00  --min_unsat_core                        false
% 3.44/1.00  --soft_assumptions                      false
% 3.44/1.00  --soft_lemma_size                       3
% 3.44/1.00  --prop_impl_unit_size                   0
% 3.44/1.00  --prop_impl_unit                        []
% 3.44/1.00  --share_sel_clauses                     true
% 3.44/1.00  --reset_solvers                         false
% 3.44/1.00  --bc_imp_inh                            [conj_cone]
% 3.44/1.00  --conj_cone_tolerance                   3.
% 3.44/1.00  --extra_neg_conj                        none
% 3.44/1.00  --large_theory_mode                     true
% 3.44/1.00  --prolific_symb_bound                   200
% 3.44/1.00  --lt_threshold                          2000
% 3.44/1.00  --clause_weak_htbl                      true
% 3.44/1.00  --gc_record_bc_elim                     false
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing Options
% 3.44/1.00  
% 3.44/1.00  --preprocessing_flag                    true
% 3.44/1.00  --time_out_prep_mult                    0.1
% 3.44/1.00  --splitting_mode                        input
% 3.44/1.00  --splitting_grd                         true
% 3.44/1.00  --splitting_cvd                         false
% 3.44/1.00  --splitting_cvd_svl                     false
% 3.44/1.00  --splitting_nvd                         32
% 3.44/1.00  --sub_typing                            true
% 3.44/1.00  --prep_gs_sim                           true
% 3.44/1.00  --prep_unflatten                        true
% 3.44/1.00  --prep_res_sim                          true
% 3.44/1.00  --prep_upred                            true
% 3.44/1.00  --prep_sem_filter                       exhaustive
% 3.44/1.00  --prep_sem_filter_out                   false
% 3.44/1.00  --pred_elim                             true
% 3.44/1.00  --res_sim_input                         true
% 3.44/1.00  --eq_ax_congr_red                       true
% 3.44/1.00  --pure_diseq_elim                       true
% 3.44/1.00  --brand_transform                       false
% 3.44/1.00  --non_eq_to_eq                          false
% 3.44/1.00  --prep_def_merge                        true
% 3.44/1.00  --prep_def_merge_prop_impl              false
% 3.44/1.00  --prep_def_merge_mbd                    true
% 3.44/1.00  --prep_def_merge_tr_red                 false
% 3.44/1.00  --prep_def_merge_tr_cl                  false
% 3.44/1.00  --smt_preprocessing                     true
% 3.44/1.00  --smt_ac_axioms                         fast
% 3.44/1.00  --preprocessed_out                      false
% 3.44/1.00  --preprocessed_stats                    false
% 3.44/1.00  
% 3.44/1.00  ------ Abstraction refinement Options
% 3.44/1.00  
% 3.44/1.00  --abstr_ref                             []
% 3.44/1.00  --abstr_ref_prep                        false
% 3.44/1.00  --abstr_ref_until_sat                   false
% 3.44/1.00  --abstr_ref_sig_restrict                funpre
% 3.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.00  --abstr_ref_under                       []
% 3.44/1.00  
% 3.44/1.00  ------ SAT Options
% 3.44/1.00  
% 3.44/1.00  --sat_mode                              false
% 3.44/1.00  --sat_fm_restart_options                ""
% 3.44/1.00  --sat_gr_def                            false
% 3.44/1.00  --sat_epr_types                         true
% 3.44/1.00  --sat_non_cyclic_types                  false
% 3.44/1.00  --sat_finite_models                     false
% 3.44/1.00  --sat_fm_lemmas                         false
% 3.44/1.00  --sat_fm_prep                           false
% 3.44/1.00  --sat_fm_uc_incr                        true
% 3.44/1.00  --sat_out_model                         small
% 3.44/1.00  --sat_out_clauses                       false
% 3.44/1.00  
% 3.44/1.00  ------ QBF Options
% 3.44/1.00  
% 3.44/1.00  --qbf_mode                              false
% 3.44/1.00  --qbf_elim_univ                         false
% 3.44/1.00  --qbf_dom_inst                          none
% 3.44/1.00  --qbf_dom_pre_inst                      false
% 3.44/1.00  --qbf_sk_in                             false
% 3.44/1.00  --qbf_pred_elim                         true
% 3.44/1.00  --qbf_split                             512
% 3.44/1.00  
% 3.44/1.00  ------ BMC1 Options
% 3.44/1.00  
% 3.44/1.00  --bmc1_incremental                      false
% 3.44/1.00  --bmc1_axioms                           reachable_all
% 3.44/1.00  --bmc1_min_bound                        0
% 3.44/1.00  --bmc1_max_bound                        -1
% 3.44/1.00  --bmc1_max_bound_default                -1
% 3.44/1.00  --bmc1_symbol_reachability              true
% 3.44/1.00  --bmc1_property_lemmas                  false
% 3.44/1.00  --bmc1_k_induction                      false
% 3.44/1.00  --bmc1_non_equiv_states                 false
% 3.44/1.00  --bmc1_deadlock                         false
% 3.44/1.00  --bmc1_ucm                              false
% 3.44/1.00  --bmc1_add_unsat_core                   none
% 3.44/1.00  --bmc1_unsat_core_children              false
% 3.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.00  --bmc1_out_stat                         full
% 3.44/1.00  --bmc1_ground_init                      false
% 3.44/1.00  --bmc1_pre_inst_next_state              false
% 3.44/1.00  --bmc1_pre_inst_state                   false
% 3.44/1.00  --bmc1_pre_inst_reach_state             false
% 3.44/1.00  --bmc1_out_unsat_core                   false
% 3.44/1.00  --bmc1_aig_witness_out                  false
% 3.44/1.00  --bmc1_verbose                          false
% 3.44/1.00  --bmc1_dump_clauses_tptp                false
% 3.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.00  --bmc1_dump_file                        -
% 3.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.00  --bmc1_ucm_extend_mode                  1
% 3.44/1.00  --bmc1_ucm_init_mode                    2
% 3.44/1.00  --bmc1_ucm_cone_mode                    none
% 3.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.00  --bmc1_ucm_relax_model                  4
% 3.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.00  --bmc1_ucm_layered_model                none
% 3.44/1.00  --bmc1_ucm_max_lemma_size               10
% 3.44/1.00  
% 3.44/1.00  ------ AIG Options
% 3.44/1.00  
% 3.44/1.00  --aig_mode                              false
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation Options
% 3.44/1.00  
% 3.44/1.00  --instantiation_flag                    true
% 3.44/1.00  --inst_sos_flag                         true
% 3.44/1.00  --inst_sos_phase                        true
% 3.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel_side                     none
% 3.44/1.00  --inst_solver_per_active                1400
% 3.44/1.00  --inst_solver_calls_frac                1.
% 3.44/1.00  --inst_passive_queue_type               priority_queues
% 3.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.00  --inst_passive_queues_freq              [25;2]
% 3.44/1.00  --inst_dismatching                      true
% 3.44/1.00  --inst_eager_unprocessed_to_passive     true
% 3.44/1.00  --inst_prop_sim_given                   true
% 3.44/1.00  --inst_prop_sim_new                     false
% 3.44/1.00  --inst_subs_new                         false
% 3.44/1.00  --inst_eq_res_simp                      false
% 3.44/1.00  --inst_subs_given                       false
% 3.44/1.00  --inst_orphan_elimination               true
% 3.44/1.00  --inst_learning_loop_flag               true
% 3.44/1.00  --inst_learning_start                   3000
% 3.44/1.00  --inst_learning_factor                  2
% 3.44/1.00  --inst_start_prop_sim_after_learn       3
% 3.44/1.00  --inst_sel_renew                        solver
% 3.44/1.00  --inst_lit_activity_flag                true
% 3.44/1.00  --inst_restr_to_given                   false
% 3.44/1.00  --inst_activity_threshold               500
% 3.44/1.00  --inst_out_proof                        true
% 3.44/1.00  
% 3.44/1.00  ------ Resolution Options
% 3.44/1.00  
% 3.44/1.00  --resolution_flag                       false
% 3.44/1.00  --res_lit_sel                           adaptive
% 3.44/1.00  --res_lit_sel_side                      none
% 3.44/1.00  --res_ordering                          kbo
% 3.44/1.00  --res_to_prop_solver                    active
% 3.44/1.00  --res_prop_simpl_new                    false
% 3.44/1.00  --res_prop_simpl_given                  true
% 3.44/1.00  --res_passive_queue_type                priority_queues
% 3.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.00  --res_passive_queues_freq               [15;5]
% 3.44/1.00  --res_forward_subs                      full
% 3.44/1.00  --res_backward_subs                     full
% 3.44/1.00  --res_forward_subs_resolution           true
% 3.44/1.00  --res_backward_subs_resolution          true
% 3.44/1.00  --res_orphan_elimination                true
% 3.44/1.00  --res_time_limit                        2.
% 3.44/1.00  --res_out_proof                         true
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Options
% 3.44/1.00  
% 3.44/1.00  --superposition_flag                    true
% 3.44/1.00  --sup_passive_queue_type                priority_queues
% 3.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.00  --demod_completeness_check              fast
% 3.44/1.00  --demod_use_ground                      true
% 3.44/1.00  --sup_to_prop_solver                    passive
% 3.44/1.00  --sup_prop_simpl_new                    true
% 3.44/1.00  --sup_prop_simpl_given                  true
% 3.44/1.00  --sup_fun_splitting                     true
% 3.44/1.00  --sup_smt_interval                      50000
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Simplification Setup
% 3.44/1.00  
% 3.44/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.44/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.44/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.44/1.00  --sup_immed_triv                        [TrivRules]
% 3.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_immed_bw_main                     []
% 3.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_input_bw                          []
% 3.44/1.00  
% 3.44/1.00  ------ Combination Options
% 3.44/1.00  
% 3.44/1.00  --comb_res_mult                         3
% 3.44/1.00  --comb_sup_mult                         2
% 3.44/1.00  --comb_inst_mult                        10
% 3.44/1.00  
% 3.44/1.00  ------ Debug Options
% 3.44/1.00  
% 3.44/1.00  --dbg_backtrace                         false
% 3.44/1.00  --dbg_dump_prop_clauses                 false
% 3.44/1.00  --dbg_dump_prop_clauses_file            -
% 3.44/1.00  --dbg_out_stat                          false
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ Proving...
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS status Theorem for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  fof(f1,axiom,(
% 3.44/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f14,plain,(
% 3.44/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.44/1.00    inference(ennf_transformation,[],[f1])).
% 3.44/1.00  
% 3.44/1.00  fof(f22,plain,(
% 3.44/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/1.00    inference(nnf_transformation,[],[f14])).
% 3.44/1.00  
% 3.44/1.00  fof(f23,plain,(
% 3.44/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/1.00    inference(rectify,[],[f22])).
% 3.44/1.00  
% 3.44/1.00  fof(f24,plain,(
% 3.44/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f25,plain,(
% 3.44/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.44/1.00  
% 3.44/1.00  fof(f43,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f25])).
% 3.44/1.00  
% 3.44/1.00  fof(f9,axiom,(
% 3.44/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f37,plain,(
% 3.44/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.44/1.00    inference(nnf_transformation,[],[f9])).
% 3.44/1.00  
% 3.44/1.00  fof(f65,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f37])).
% 3.44/1.00  
% 3.44/1.00  fof(f4,axiom,(
% 3.44/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f16,plain,(
% 3.44/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.44/1.00    inference(ennf_transformation,[],[f4])).
% 3.44/1.00  
% 3.44/1.00  fof(f49,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f16])).
% 3.44/1.00  
% 3.44/1.00  fof(f12,conjecture,(
% 3.44/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f13,negated_conjecture,(
% 3.44/1.00    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.44/1.00    inference(negated_conjecture,[],[f12])).
% 3.44/1.00  
% 3.44/1.00  fof(f21,plain,(
% 3.44/1.00    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.44/1.00    inference(ennf_transformation,[],[f13])).
% 3.44/1.00  
% 3.44/1.00  fof(f38,plain,(
% 3.44/1.00    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.44/1.00    inference(nnf_transformation,[],[f21])).
% 3.44/1.00  
% 3.44/1.00  fof(f39,plain,(
% 3.44/1.00    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.44/1.00    inference(flattening,[],[f38])).
% 3.44/1.00  
% 3.44/1.00  fof(f40,plain,(
% 3.44/1.00    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | r1_tarski(k2_tarski(sK3,sK4),sK5)))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f41,plain,(
% 3.44/1.00    (~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | r1_tarski(k2_tarski(sK3,sK4),sK5))),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f40])).
% 3.44/1.00  
% 3.44/1.00  fof(f70,plain,(
% 3.44/1.00    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.44/1.00    inference(cnf_transformation,[],[f41])).
% 3.44/1.00  
% 3.44/1.00  fof(f8,axiom,(
% 3.44/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f63,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f8])).
% 3.44/1.00  
% 3.44/1.00  fof(f73,plain,(
% 3.44/1.00    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5)),
% 3.44/1.00    inference(definition_unfolding,[],[f70,f63])).
% 3.44/1.00  
% 3.44/1.00  fof(f64,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f37])).
% 3.44/1.00  
% 3.44/1.00  fof(f2,axiom,(
% 3.44/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f26,plain,(
% 3.44/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.44/1.00    inference(nnf_transformation,[],[f2])).
% 3.44/1.00  
% 3.44/1.00  fof(f27,plain,(
% 3.44/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.44/1.00    inference(flattening,[],[f26])).
% 3.44/1.00  
% 3.44/1.00  fof(f45,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.44/1.00    inference(cnf_transformation,[],[f27])).
% 3.44/1.00  
% 3.44/1.00  fof(f77,plain,(
% 3.44/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.44/1.00    inference(equality_resolution,[],[f45])).
% 3.44/1.00  
% 3.44/1.00  fof(f69,plain,(
% 3.44/1.00    r2_hidden(sK4,sK5) | r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.44/1.00    inference(cnf_transformation,[],[f41])).
% 3.44/1.00  
% 3.44/1.00  fof(f74,plain,(
% 3.44/1.00    r2_hidden(sK4,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5)),
% 3.44/1.00    inference(definition_unfolding,[],[f69,f63])).
% 3.44/1.00  
% 3.44/1.00  fof(f42,plain,(
% 3.44/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f25])).
% 3.44/1.00  
% 3.44/1.00  fof(f6,axiom,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f19,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.44/1.00    inference(ennf_transformation,[],[f6])).
% 3.44/1.00  
% 3.44/1.00  fof(f28,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.44/1.00    inference(nnf_transformation,[],[f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f29,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.44/1.00    inference(flattening,[],[f28])).
% 3.44/1.00  
% 3.44/1.00  fof(f30,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.44/1.00    inference(rectify,[],[f29])).
% 3.44/1.00  
% 3.44/1.00  fof(f31,plain,(
% 3.44/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f32,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.44/1.00  
% 3.44/1.00  fof(f54,plain,(
% 3.44/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.44/1.00    inference(cnf_transformation,[],[f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f78,plain,(
% 3.44/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 3.44/1.00    inference(equality_resolution,[],[f54])).
% 3.44/1.00  
% 3.44/1.00  fof(f79,plain,(
% 3.44/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 3.44/1.00    inference(equality_resolution,[],[f78])).
% 3.44/1.00  
% 3.44/1.00  fof(f68,plain,(
% 3.44/1.00    r2_hidden(sK3,sK5) | r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.44/1.00    inference(cnf_transformation,[],[f41])).
% 3.44/1.00  
% 3.44/1.00  fof(f75,plain,(
% 3.44/1.00    r2_hidden(sK3,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5)),
% 3.44/1.00    inference(definition_unfolding,[],[f68,f63])).
% 3.44/1.00  
% 3.44/1.00  fof(f10,axiom,(
% 3.44/1.00    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f66,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f10])).
% 3.44/1.00  
% 3.44/1.00  fof(f71,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1))) )),
% 3.44/1.00    inference(definition_unfolding,[],[f66,f63])).
% 3.44/1.00  
% 3.44/1.00  fof(f3,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f15,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.44/1.00    inference(ennf_transformation,[],[f3])).
% 3.44/1.00  
% 3.44/1.00  fof(f48,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f15])).
% 3.44/1.00  
% 3.44/1.00  fof(f51,plain,(
% 3.44/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.44/1.00    inference(cnf_transformation,[],[f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f84,plain,(
% 3.44/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 3.44/1.00    inference(equality_resolution,[],[f51])).
% 3.44/1.00  
% 3.44/1.00  fof(f44,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f25])).
% 3.44/1.00  
% 3.44/1.00  fof(f47,plain,(
% 3.44/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f27])).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1,plain,
% 3.44/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1141,plain,
% 3.44/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_21,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1122,plain,
% 3.44/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.44/1.00      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7,plain,
% 3.44/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.44/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1136,plain,
% 3.44/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1933,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 3.44/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1122,c_1136]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3953,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(sK0(X0,X1)),X0) = X0
% 3.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1141,c_1933]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_25,negated_conjecture,
% 3.44/1.00      ( ~ r2_hidden(sK3,sK5)
% 3.44/1.00      | ~ r2_hidden(sK4,sK5)
% 3.44/1.00      | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.44/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1118,plain,
% 3.44/1.00      ( r2_hidden(sK3,sK5) != iProver_top
% 3.44/1.00      | r2_hidden(sK4,sK5) != iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6799,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK3,sK3,sK4),sK5)),k1_enumset1(sK3,sK3,sK4)) = k1_enumset1(sK3,sK3,sK4)
% 3.44/1.00      | r2_hidden(sK3,sK5) != iProver_top
% 3.44/1.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3953,c_1118]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_22,plain,
% 3.44/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1173,plain,
% 3.44/1.00      ( r2_hidden(sK3,sK5) | ~ r1_tarski(k1_tarski(sK3),sK5) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1174,plain,
% 3.44/1.00      ( r2_hidden(sK3,sK5) = iProver_top
% 3.44/1.00      | r1_tarski(k1_tarski(sK3),sK5) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5,plain,
% 3.44/1.00      ( r1_tarski(X0,X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1138,plain,
% 3.44/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_26,negated_conjecture,
% 3.44/1.00      ( r2_hidden(sK4,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.44/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1117,plain,
% 3.44/1.00      ( r2_hidden(sK4,sK5) = iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1633,plain,
% 3.44/1.00      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
% 3.44/1.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1117,c_1136]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.44/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1140,plain,
% 3.44/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.44/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.44/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2720,plain,
% 3.44/1.00      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
% 3.44/1.00      | r2_hidden(sK4,X0) = iProver_top
% 3.44/1.00      | r1_tarski(sK5,X0) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1633,c_1140]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_29,plain,
% 3.44/1.00      ( r2_hidden(sK4,sK5) = iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1219,plain,
% 3.44/1.00      ( ~ r2_hidden(sK4,X0) | r2_hidden(sK4,sK5) | ~ r1_tarski(X0,sK5) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1265,plain,
% 3.44/1.00      ( ~ r2_hidden(sK4,k1_enumset1(X0,X1,sK4))
% 3.44/1.00      | r2_hidden(sK4,sK5)
% 3.44/1.00      | ~ r1_tarski(k1_enumset1(X0,X1,sK4),sK5) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1266,plain,
% 3.44/1.00      ( r2_hidden(sK4,k1_enumset1(X0,X1,sK4)) != iProver_top
% 3.44/1.00      | r2_hidden(sK4,sK5) = iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(X0,X1,sK4),sK5) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1268,plain,
% 3.44/1.00      ( r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4)) != iProver_top
% 3.44/1.00      | r2_hidden(sK4,sK5) = iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_1266]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1262,plain,
% 3.44/1.00      ( ~ r2_hidden(sK4,X0) | r2_hidden(sK4,X1) | ~ r1_tarski(X0,X1) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1368,plain,
% 3.44/1.00      ( r2_hidden(sK4,X0) | ~ r2_hidden(sK4,sK5) | ~ r1_tarski(sK5,X0) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_1262]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1369,plain,
% 3.44/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 3.44/1.00      | r2_hidden(sK4,sK5) != iProver_top
% 3.44/1.00      | r1_tarski(sK5,X0) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1368]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13,plain,
% 3.44/1.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3057,plain,
% 3.44/1.00      ( r2_hidden(sK4,k1_enumset1(X0,X1,sK4)) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3058,plain,
% 3.44/1.00      ( r2_hidden(sK4,k1_enumset1(X0,X1,sK4)) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3057]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3060,plain,
% 3.44/1.00      ( r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4)) = iProver_top ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_3058]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3116,plain,
% 3.44/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 3.44/1.00      | r1_tarski(sK5,X0) != iProver_top ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_2720,c_29,c_1268,c_1369,c_3060]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3122,plain,
% 3.44/1.00      ( r2_hidden(sK4,sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1138,c_3116]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_27,negated_conjecture,
% 3.44/1.00      ( r2_hidden(sK3,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.44/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1116,plain,
% 3.44/1.00      ( r2_hidden(sK3,sK5) = iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1634,plain,
% 3.44/1.00      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
% 3.44/1.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1116,c_1136]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3962,plain,
% 3.44/1.00      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
% 3.44/1.00      | k2_xboole_0(k1_tarski(sK3),sK5) = sK5 ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1634,c_1933]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_23,plain,
% 3.44/1.00      ( r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1120,plain,
% 3.44/1.00      ( r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1632,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X0,X1) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1120,c_1136]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6,plain,
% 3.44/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1137,plain,
% 3.44/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.44/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2122,plain,
% 3.44/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1138,c_1137]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2322,plain,
% 3.44/1.00      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2122,c_1137]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1121,plain,
% 3.44/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.44/1.00      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2547,plain,
% 3.44/1.00      ( r2_hidden(X0,k2_xboole_0(k2_xboole_0(k1_tarski(X0),X1),X2)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2322,c_1121]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2565,plain,
% 3.44/1.00      ( r2_hidden(X0,k2_xboole_0(k1_enumset1(X0,X0,X1),X2)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1632,c_2547]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4226,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(sK3),sK5) = sK5
% 3.44/1.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3962,c_2565]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_30,plain,
% 3.44/1.00      ( r2_hidden(sK3,sK5) != iProver_top
% 3.44/1.00      | r2_hidden(sK4,sK5) != iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4224,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(sK3),sK5) = sK5
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3962,c_2122]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4353,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(sK3),sK5) = sK5 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_4226,c_29,c_30,c_1268,c_3060,c_4224]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4357,plain,
% 3.44/1.00      ( r1_tarski(k1_tarski(sK3),sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_4353,c_2122]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7184,plain,
% 3.44/1.00      ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK3,sK3,sK4),sK5)),k1_enumset1(sK3,sK3,sK4)) = k1_enumset1(sK3,sK3,sK4) ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_6799,c_29,c_1174,c_1268,c_3060,c_4357]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2323,plain,
% 3.44/1.00      ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2122,c_1121]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7195,plain,
% 3.44/1.00      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),k1_enumset1(sK3,sK3,sK4)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_7184,c_2323]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_16,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 3.44/1.00      | X0 = X1
% 3.44/1.00      | X0 = X2
% 3.44/1.00      | X0 = X3 ),
% 3.44/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1127,plain,
% 3.44/1.00      ( X0 = X1
% 3.44/1.00      | X0 = X2
% 3.44/1.00      | X0 = X3
% 3.44/1.00      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7223,plain,
% 3.44/1.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK3
% 3.44/1.00      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK4 ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_7195,c_1127]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_0,plain,
% 3.44/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1299,plain,
% 3.44/1.00      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1308,plain,
% 3.44/1.00      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5) != iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3,plain,
% 3.44/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1467,plain,
% 3.44/1.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1980,plain,
% 3.44/1.00      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_1467]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3017,plain,
% 3.44/1.00      ( r1_tarski(sK5,sK5) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_584,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.44/1.00      theory(equality) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2100,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,X1)
% 3.44/1.00      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.44/1.00      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 3.44/1.00      | sK5 != X1 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_584]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3149,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,sK5)
% 3.44/1.00      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.44/1.00      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 3.44/1.00      | sK5 != sK5 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_2100]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3150,plain,
% 3.44/1.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 3.44/1.00      | sK5 != sK5
% 3.44/1.00      | r2_hidden(X0,sK5) != iProver_top
% 3.44/1.00      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3149]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3152,plain,
% 3.44/1.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) != sK3
% 3.44/1.00      | sK5 != sK5
% 3.44/1.00      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5) = iProver_top
% 3.44/1.00      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_3150]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11405,plain,
% 3.44/1.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK4 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_7223,c_29,c_30,c_1174,c_1268,c_1308,c_1980,c_3017,
% 3.44/1.00                 c_3060,c_3152,c_4357]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1142,plain,
% 3.44/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11498,plain,
% 3.44/1.00      ( r2_hidden(sK4,sK5) != iProver_top
% 3.44/1.00      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_11405,c_1142]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(contradiction,plain,
% 3.44/1.00      ( $false ),
% 3.44/1.00      inference(minisat,[status(thm)],[c_11498,c_4357,c_3122,c_1174,c_30]) ).
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  ------                               Statistics
% 3.44/1.00  
% 3.44/1.00  ------ General
% 3.44/1.00  
% 3.44/1.00  abstr_ref_over_cycles:                  0
% 3.44/1.00  abstr_ref_under_cycles:                 0
% 3.44/1.00  gc_basic_clause_elim:                   0
% 3.44/1.00  forced_gc_time:                         0
% 3.44/1.00  parsing_time:                           0.008
% 3.44/1.00  unif_index_cands_time:                  0.
% 3.44/1.00  unif_index_add_time:                    0.
% 3.44/1.00  orderings_time:                         0.
% 3.44/1.00  out_proof_time:                         0.011
% 3.44/1.00  total_time:                             0.324
% 3.44/1.00  num_of_symbols:                         42
% 3.44/1.00  num_of_terms:                           10693
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing
% 3.44/1.00  
% 3.44/1.00  num_of_splits:                          0
% 3.44/1.00  num_of_split_atoms:                     0
% 3.44/1.00  num_of_reused_defs:                     0
% 3.44/1.00  num_eq_ax_congr_red:                    33
% 3.44/1.00  num_of_sem_filtered_clauses:            1
% 3.44/1.00  num_of_subtypes:                        0
% 3.44/1.00  monotx_restored_types:                  0
% 3.44/1.00  sat_num_of_epr_types:                   0
% 3.44/1.00  sat_num_of_non_cyclic_types:            0
% 3.44/1.00  sat_guarded_non_collapsed_types:        0
% 3.44/1.00  num_pure_diseq_elim:                    0
% 3.44/1.00  simp_replaced_by:                       0
% 3.44/1.00  res_preprocessed:                       119
% 3.44/1.00  prep_upred:                             0
% 3.44/1.00  prep_unflattend:                        0
% 3.44/1.00  smt_new_axioms:                         0
% 3.44/1.00  pred_elim_cands:                        2
% 3.44/1.00  pred_elim:                              0
% 3.44/1.00  pred_elim_cl:                           0
% 3.44/1.00  pred_elim_cycles:                       2
% 3.44/1.00  merged_defs:                            8
% 3.44/1.00  merged_defs_ncl:                        0
% 3.44/1.00  bin_hyper_res:                          8
% 3.44/1.00  prep_cycles:                            4
% 3.44/1.00  pred_elim_time:                         0.
% 3.44/1.00  splitting_time:                         0.
% 3.44/1.00  sem_filter_time:                        0.
% 3.44/1.00  monotx_time:                            0.
% 3.44/1.00  subtype_inf_time:                       0.
% 3.44/1.00  
% 3.44/1.00  ------ Problem properties
% 3.44/1.00  
% 3.44/1.00  clauses:                                27
% 3.44/1.00  conjectures:                            3
% 3.44/1.00  epr:                                    4
% 3.44/1.00  horn:                                   20
% 3.44/1.00  ground:                                 3
% 3.44/1.00  unary:                                  6
% 3.44/1.00  binary:                                 9
% 3.44/1.00  lits:                                   63
% 3.44/1.00  lits_eq:                                22
% 3.44/1.00  fd_pure:                                0
% 3.44/1.00  fd_pseudo:                              0
% 3.44/1.00  fd_cond:                                0
% 3.44/1.00  fd_pseudo_cond:                         8
% 3.44/1.00  ac_symbols:                             0
% 3.44/1.00  
% 3.44/1.00  ------ Propositional Solver
% 3.44/1.00  
% 3.44/1.00  prop_solver_calls:                      34
% 3.44/1.00  prop_fast_solver_calls:                 869
% 3.44/1.00  smt_solver_calls:                       0
% 3.44/1.00  smt_fast_solver_calls:                  0
% 3.44/1.00  prop_num_of_clauses:                    4712
% 3.44/1.00  prop_preprocess_simplified:             10524
% 3.44/1.00  prop_fo_subsumed:                       18
% 3.44/1.00  prop_solver_time:                       0.
% 3.44/1.00  smt_solver_time:                        0.
% 3.44/1.00  smt_fast_solver_time:                   0.
% 3.44/1.00  prop_fast_solver_time:                  0.
% 3.44/1.00  prop_unsat_core_time:                   0.
% 3.44/1.00  
% 3.44/1.00  ------ QBF
% 3.44/1.00  
% 3.44/1.00  qbf_q_res:                              0
% 3.44/1.00  qbf_num_tautologies:                    0
% 3.44/1.00  qbf_prep_cycles:                        0
% 3.44/1.00  
% 3.44/1.00  ------ BMC1
% 3.44/1.00  
% 3.44/1.00  bmc1_current_bound:                     -1
% 3.44/1.00  bmc1_last_solved_bound:                 -1
% 3.44/1.00  bmc1_unsat_core_size:                   -1
% 3.44/1.00  bmc1_unsat_core_parents_size:           -1
% 3.44/1.00  bmc1_merge_next_fun:                    0
% 3.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation
% 3.44/1.00  
% 3.44/1.00  inst_num_of_clauses:                    1087
% 3.44/1.00  inst_num_in_passive:                    598
% 3.44/1.00  inst_num_in_active:                     414
% 3.44/1.00  inst_num_in_unprocessed:                75
% 3.44/1.00  inst_num_of_loops:                      720
% 3.44/1.00  inst_num_of_learning_restarts:          0
% 3.44/1.00  inst_num_moves_active_passive:          300
% 3.44/1.00  inst_lit_activity:                      0
% 3.44/1.00  inst_lit_activity_moves:                0
% 3.44/1.00  inst_num_tautologies:                   0
% 3.44/1.00  inst_num_prop_implied:                  0
% 3.44/1.00  inst_num_existing_simplified:           0
% 3.44/1.01  inst_num_eq_res_simplified:             0
% 3.44/1.01  inst_num_child_elim:                    0
% 3.44/1.01  inst_num_of_dismatching_blockings:      783
% 3.44/1.01  inst_num_of_non_proper_insts:           1662
% 3.44/1.01  inst_num_of_duplicates:                 0
% 3.44/1.01  inst_inst_num_from_inst_to_res:         0
% 3.44/1.01  inst_dismatching_checking_time:         0.
% 3.44/1.01  
% 3.44/1.01  ------ Resolution
% 3.44/1.01  
% 3.44/1.01  res_num_of_clauses:                     0
% 3.44/1.01  res_num_in_passive:                     0
% 3.44/1.01  res_num_in_active:                      0
% 3.44/1.01  res_num_of_loops:                       123
% 3.44/1.01  res_forward_subset_subsumed:            127
% 3.44/1.01  res_backward_subset_subsumed:           2
% 3.44/1.01  res_forward_subsumed:                   0
% 3.44/1.01  res_backward_subsumed:                  0
% 3.44/1.01  res_forward_subsumption_resolution:     0
% 3.44/1.01  res_backward_subsumption_resolution:    0
% 3.44/1.01  res_clause_to_clause_subsumption:       2155
% 3.44/1.01  res_orphan_elimination:                 0
% 3.44/1.01  res_tautology_del:                      154
% 3.44/1.01  res_num_eq_res_simplified:              0
% 3.44/1.01  res_num_sel_changes:                    0
% 3.44/1.01  res_moves_from_active_to_pass:          0
% 3.44/1.01  
% 3.44/1.01  ------ Superposition
% 3.44/1.01  
% 3.44/1.01  sup_time_total:                         0.
% 3.44/1.01  sup_time_generating:                    0.
% 3.44/1.01  sup_time_sim_full:                      0.
% 3.44/1.01  sup_time_sim_immed:                     0.
% 3.44/1.01  
% 3.44/1.01  sup_num_of_clauses:                     374
% 3.44/1.01  sup_num_in_active:                      96
% 3.44/1.01  sup_num_in_passive:                     278
% 3.44/1.01  sup_num_of_loops:                       142
% 3.44/1.01  sup_fw_superposition:                   665
% 3.44/1.01  sup_bw_superposition:                   373
% 3.44/1.01  sup_immediate_simplified:               144
% 3.44/1.01  sup_given_eliminated:                   0
% 3.44/1.01  comparisons_done:                       0
% 3.44/1.01  comparisons_avoided:                    13
% 3.44/1.01  
% 3.44/1.01  ------ Simplifications
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  sim_fw_subset_subsumed:                 7
% 3.44/1.01  sim_bw_subset_subsumed:                 14
% 3.44/1.01  sim_fw_subsumed:                        34
% 3.44/1.01  sim_bw_subsumed:                        14
% 3.44/1.01  sim_fw_subsumption_res:                 0
% 3.44/1.01  sim_bw_subsumption_res:                 0
% 3.44/1.01  sim_tautology_del:                      9
% 3.44/1.01  sim_eq_tautology_del:                   33
% 3.44/1.01  sim_eq_res_simp:                        0
% 3.44/1.01  sim_fw_demodulated:                     82
% 3.44/1.01  sim_bw_demodulated:                     28
% 3.44/1.01  sim_light_normalised:                   49
% 3.44/1.01  sim_joinable_taut:                      0
% 3.44/1.01  sim_joinable_simp:                      0
% 3.44/1.01  sim_ac_normalised:                      0
% 3.44/1.01  sim_smt_subsumption:                    0
% 3.44/1.01  
%------------------------------------------------------------------------------
