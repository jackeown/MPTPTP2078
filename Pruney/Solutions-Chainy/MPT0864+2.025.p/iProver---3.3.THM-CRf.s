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
% DateTime   : Thu Dec  3 11:57:51 EST 2020

% Result     : Theorem 19.32s
% Output     : CNFRefutation 19.32s
% Verified   : 
% Statistics : Number of formulae       :  138 (7797 expanded)
%              Number of clauses        :   84 (2001 expanded)
%              Number of leaves         :   14 (2001 expanded)
%              Depth                    :   35
%              Number of atoms          :  394 (31080 expanded)
%              Number of equality atoms :  316 (22933 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f64,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f65,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f64])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f22])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f66,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f67,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f66])).

fof(f9,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK4,sK5) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK3) = sK3
        | k1_mcart_1(sK3) = sK3 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK3 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( k2_mcart_1(sK3) = sK3
      | k1_mcart_1(sK3) = sK3 )
    & k4_tarski(sK4,sK5) = sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f25,f24])).

fof(f47,plain,
    ( k2_mcart_1(sK3) = sK3
    | k1_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f49])).

fof(f63,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f40,f49])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_113638,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_113633,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_113636,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X2,X2,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_113948,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X1)) = X1
    | sK2(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_113633,c_113636])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_113635,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_114025,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | k4_tarski(X2,X3) != X0
    | sK2(k2_enumset1(X0,X0,X0,X1)) = X1
    | r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_113948,c_113635])).

cnf(c_114958,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X2) = k1_xboole_0
    | sK2(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X2)) = X2
    | r2_hidden(X1,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X2)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_114025])).

cnf(c_116667,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1) = k1_xboole_0
    | sK2(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_113638,c_114958])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_113637,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,negated_conjecture,
    ( k1_mcart_1(sK3) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_113718,plain,
    ( k1_mcart_1(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_17,c_12])).

cnf(c_113726,plain,
    ( k2_mcart_1(sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_16,c_113718])).

cnf(c_11,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_113710,plain,
    ( k2_mcart_1(sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_17,c_11])).

cnf(c_113728,plain,
    ( sK5 = sK3
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_113726,c_113710])).

cnf(c_113829,plain,
    ( sK2(X0) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_113635])).

cnf(c_114022,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X1)) = X1
    | sK3 != X0
    | r2_hidden(sK5,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_113948,c_113829])).

cnf(c_114160,plain,
    ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
    | sK2(k2_enumset1(sK3,sK3,sK3,X0)) = X0
    | r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,X0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_114022])).

cnf(c_114359,plain,
    ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
    | sK2(k2_enumset1(sK3,sK3,sK3,X0)) = X0
    | sK4 = sK3
    | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_113728,c_114160])).

cnf(c_114434,plain,
    ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
    | sK2(k2_enumset1(sK3,sK3,sK3,X0)) = X0
    | sK4 = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_114359,c_113637])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_113634,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_114442,plain,
    ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
    | k4_tarski(X1,X2) != X0
    | sK4 = sK3
    | r2_hidden(X1,k2_enumset1(sK3,sK3,sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_114434,c_113634])).

cnf(c_115485,plain,
    ( k2_enumset1(sK3,sK3,sK3,k4_tarski(X0,X1)) = k1_xboole_0
    | sK4 = sK3
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,k4_tarski(X0,X1))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_114442])).

cnf(c_115607,plain,
    ( k2_enumset1(sK3,sK3,sK3,k4_tarski(sK3,X0)) = k1_xboole_0
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_113637,c_115485])).

cnf(c_115786,plain,
    ( sK4 = sK3
    | r2_hidden(k4_tarski(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_115607,c_113638])).

cnf(c_113740,plain,
    ( k4_tarski(sK4,sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_113728,c_17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_113639,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_113777,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_113633,c_113639])).

cnf(c_113881,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k4_tarski(X1,X2) != X0
    | r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_113777,c_113635])).

cnf(c_113971,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k1_xboole_0
    | r2_hidden(X1,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_113881])).

cnf(c_114277,plain,
    ( k2_enumset1(k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3)) = k1_xboole_0
    | sK4 = sK3
    | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_113740,c_113971])).

cnf(c_31,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_33,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_114298,plain,
    ( sK4 = sK3
    | k2_enumset1(k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_114277,c_33])).

cnf(c_114299,plain,
    ( k2_enumset1(k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3)) = k1_xboole_0
    | sK4 = sK3 ),
    inference(renaming,[status(thm)],[c_114298])).

cnf(c_114314,plain,
    ( k4_tarski(sK4,sK3) = X0
    | sK4 = sK3
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_114299,c_113636])).

cnf(c_115810,plain,
    ( k4_tarski(sK3,X0) = k4_tarski(sK4,sK3)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_115786,c_114314])).

cnf(c_116137,plain,
    ( k1_mcart_1(k4_tarski(sK3,X0)) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_115810,c_12])).

cnf(c_116240,plain,
    ( sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_116137,c_12])).

cnf(c_113792,plain,
    ( sK2(X0) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_113634])).

cnf(c_116295,plain,
    ( sK2(X0) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_116240,c_113792])).

cnf(c_116709,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1) = k1_xboole_0
    | sK3 != X1
    | r2_hidden(sK3,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_116667,c_116295])).

cnf(c_116802,plain,
    ( k2_enumset1(k4_tarski(X0,sK3),k4_tarski(X0,sK3),k4_tarski(X0,sK3),sK3) = k1_xboole_0
    | r2_hidden(sK3,k2_enumset1(k4_tarski(X0,sK3),k4_tarski(X0,sK3),k4_tarski(X0,sK3),sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_116709])).

cnf(c_116813,plain,
    ( k2_enumset1(k4_tarski(X0,sK3),k4_tarski(X0,sK3),k4_tarski(X0,sK3),sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_116802,c_113638])).

cnf(c_116817,plain,
    ( r2_hidden(k4_tarski(X0,sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_116813,c_113637])).

cnf(c_114030,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X1)) = X0
    | sK3 != X1
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_113948,c_113792])).

cnf(c_114204,plain,
    ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,sK3)) = X0
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_114030])).

cnf(c_114423,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK3) = k1_xboole_0
    | sK2(k2_enumset1(sK4,sK4,sK4,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_113637,c_114204])).

cnf(c_114684,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK3) = k1_xboole_0
    | sK4 != sK3
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_114423,c_113792])).

cnf(c_114761,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK3) = k1_xboole_0
    | sK4 != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_114684,c_113637])).

cnf(c_116280,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_116240,c_114761])).

cnf(c_116349,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_116280])).

cnf(c_116633,plain,
    ( sK3 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_116349,c_113636])).

cnf(c_116894,plain,
    ( k4_tarski(X0,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_116817,c_116633])).

cnf(c_117154,plain,
    ( k1_mcart_1(sK3) = X0 ),
    inference(superposition,[status(thm)],[c_116894,c_12])).

cnf(c_117499,plain,
    ( k1_mcart_1(sK3) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_117154,c_116295])).

cnf(c_117501,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(sK3),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_117154,c_113633])).

cnf(c_116297,plain,
    ( k1_mcart_1(sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_116240,c_113718])).

cnf(c_117569,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_117501,c_116297])).

cnf(c_117582,plain,
    ( k1_mcart_1(sK3) != sK3
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_117499,c_117569])).

cnf(c_117583,plain,
    ( sK3 != sK3
    | k1_xboole_0 = X0 ),
    inference(light_normalisation,[status(thm)],[c_117582,c_116297])).

cnf(c_117584,plain,
    ( k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_117583])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_116627,plain,
    ( k2_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_116349,c_10])).

cnf(c_117507,plain,
    ( k1_mcart_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_117154,c_116627])).

cnf(c_117541,plain,
    ( sK3 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_117507,c_116297])).

cnf(c_116284,plain,
    ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,sK3)) = X0
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_116240,c_114204])).

cnf(c_116458,plain,
    ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,sK3)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_116284,c_113638])).

cnf(c_116462,plain,
    ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
    | sK3 != X0
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_116458,c_116295])).

cnf(c_116521,plain,
    ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
    | sK3 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_116462,c_113638])).

cnf(c_117511,plain,
    ( k1_mcart_1(sK3) = k1_xboole_0
    | sK3 != X0 ),
    inference(demodulation,[status(thm)],[c_117154,c_116521])).

cnf(c_117537,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_117511,c_116297])).

cnf(c_117545,plain,
    ( sK3 != X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_117541,c_117537])).

cnf(c_117588,plain,
    ( k1_xboole_0 != X0 ),
    inference(demodulation,[status(thm)],[c_117584,c_117545])).

cnf(c_117591,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_117588,c_117584])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 14:21:45 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 19.32/3.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.32/3.04  
% 19.32/3.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.32/3.04  
% 19.32/3.04  ------  iProver source info
% 19.32/3.04  
% 19.32/3.04  git: date: 2020-06-30 10:37:57 +0100
% 19.32/3.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.32/3.04  git: non_committed_changes: false
% 19.32/3.04  git: last_make_outside_of_git: false
% 19.32/3.04  
% 19.32/3.04  ------ 
% 19.32/3.04  ------ Parsing...
% 19.32/3.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  ------ Proving...
% 19.32/3.04  ------ Problem Properties 
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  clauses                                 18
% 19.32/3.04  conjectures                             3
% 19.32/3.04  EPR                                     0
% 19.32/3.04  Horn                                    13
% 19.32/3.04  unary                                   7
% 19.32/3.04  binary                                  3
% 19.32/3.04  lits                                    38
% 19.32/3.04  lits eq                                 25
% 19.32/3.04  fd_pure                                 0
% 19.32/3.04  fd_pseudo                               0
% 19.32/3.04  fd_cond                                 3
% 19.32/3.04  fd_pseudo_cond                          5
% 19.32/3.04  AC symbols                              0
% 19.32/3.04  
% 19.32/3.04  ------ Input Options Time Limit: Unbounded
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.32/3.04  Current options:
% 19.32/3.04  ------ 
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.32/3.04  
% 19.32/3.04  ------ Proving...
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  % SZS status Theorem for theBenchmark.p
% 19.32/3.04  
% 19.32/3.04   Resolution empty clause
% 19.32/3.04  
% 19.32/3.04  % SZS output start CNFRefutation for theBenchmark.p
% 19.32/3.04  
% 19.32/3.04  fof(f2,axiom,(
% 19.32/3.04    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f17,plain,(
% 19.32/3.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.32/3.04    inference(nnf_transformation,[],[f2])).
% 19.32/3.04  
% 19.32/3.04  fof(f18,plain,(
% 19.32/3.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.32/3.04    inference(flattening,[],[f17])).
% 19.32/3.04  
% 19.32/3.04  fof(f19,plain,(
% 19.32/3.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.32/3.04    inference(rectify,[],[f18])).
% 19.32/3.04  
% 19.32/3.04  fof(f20,plain,(
% 19.32/3.04    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.32/3.04    introduced(choice_axiom,[])).
% 19.32/3.04  
% 19.32/3.04  fof(f21,plain,(
% 19.32/3.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.32/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 19.32/3.04  
% 19.32/3.04  fof(f33,plain,(
% 19.32/3.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.32/3.04    inference(cnf_transformation,[],[f21])).
% 19.32/3.04  
% 19.32/3.04  fof(f4,axiom,(
% 19.32/3.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f38,plain,(
% 19.32/3.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.32/3.04    inference(cnf_transformation,[],[f4])).
% 19.32/3.04  
% 19.32/3.04  fof(f5,axiom,(
% 19.32/3.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f39,plain,(
% 19.32/3.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.32/3.04    inference(cnf_transformation,[],[f5])).
% 19.32/3.04  
% 19.32/3.04  fof(f48,plain,(
% 19.32/3.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.32/3.04    inference(definition_unfolding,[],[f38,f39])).
% 19.32/3.04  
% 19.32/3.04  fof(f57,plain,(
% 19.32/3.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.32/3.04    inference(definition_unfolding,[],[f33,f48])).
% 19.32/3.04  
% 19.32/3.04  fof(f64,plain,(
% 19.32/3.04    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 19.32/3.04    inference(equality_resolution,[],[f57])).
% 19.32/3.04  
% 19.32/3.04  fof(f65,plain,(
% 19.32/3.04    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 19.32/3.04    inference(equality_resolution,[],[f64])).
% 19.32/3.04  
% 19.32/3.04  fof(f8,axiom,(
% 19.32/3.04    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f11,plain,(
% 19.32/3.04    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 19.32/3.04    inference(ennf_transformation,[],[f8])).
% 19.32/3.04  
% 19.32/3.04  fof(f22,plain,(
% 19.32/3.04    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 19.32/3.04    introduced(choice_axiom,[])).
% 19.32/3.04  
% 19.32/3.04  fof(f23,plain,(
% 19.32/3.04    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 19.32/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f22])).
% 19.32/3.04  
% 19.32/3.04  fof(f43,plain,(
% 19.32/3.04    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 19.32/3.04    inference(cnf_transformation,[],[f23])).
% 19.32/3.04  
% 19.32/3.04  fof(f31,plain,(
% 19.32/3.04    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 19.32/3.04    inference(cnf_transformation,[],[f21])).
% 19.32/3.04  
% 19.32/3.04  fof(f59,plain,(
% 19.32/3.04    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.32/3.04    inference(definition_unfolding,[],[f31,f48])).
% 19.32/3.04  
% 19.32/3.04  fof(f68,plain,(
% 19.32/3.04    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 19.32/3.04    inference(equality_resolution,[],[f59])).
% 19.32/3.04  
% 19.32/3.04  fof(f45,plain,(
% 19.32/3.04    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 19.32/3.04    inference(cnf_transformation,[],[f23])).
% 19.32/3.04  
% 19.32/3.04  fof(f32,plain,(
% 19.32/3.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.32/3.04    inference(cnf_transformation,[],[f21])).
% 19.32/3.04  
% 19.32/3.04  fof(f58,plain,(
% 19.32/3.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.32/3.04    inference(definition_unfolding,[],[f32,f48])).
% 19.32/3.04  
% 19.32/3.04  fof(f66,plain,(
% 19.32/3.04    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 19.32/3.04    inference(equality_resolution,[],[f58])).
% 19.32/3.04  
% 19.32/3.04  fof(f67,plain,(
% 19.32/3.04    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 19.32/3.04    inference(equality_resolution,[],[f66])).
% 19.32/3.04  
% 19.32/3.04  fof(f9,conjecture,(
% 19.32/3.04    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f10,negated_conjecture,(
% 19.32/3.04    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 19.32/3.04    inference(negated_conjecture,[],[f9])).
% 19.32/3.04  
% 19.32/3.04  fof(f12,plain,(
% 19.32/3.04    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 19.32/3.04    inference(ennf_transformation,[],[f10])).
% 19.32/3.04  
% 19.32/3.04  fof(f25,plain,(
% 19.32/3.04    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK4,sK5) = X0) )),
% 19.32/3.04    introduced(choice_axiom,[])).
% 19.32/3.04  
% 19.32/3.04  fof(f24,plain,(
% 19.32/3.04    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & ? [X2,X1] : k4_tarski(X1,X2) = sK3)),
% 19.32/3.04    introduced(choice_axiom,[])).
% 19.32/3.04  
% 19.32/3.04  fof(f26,plain,(
% 19.32/3.04    (k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & k4_tarski(sK4,sK5) = sK3),
% 19.32/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f25,f24])).
% 19.32/3.04  
% 19.32/3.04  fof(f47,plain,(
% 19.32/3.04    k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3),
% 19.32/3.04    inference(cnf_transformation,[],[f26])).
% 19.32/3.04  
% 19.32/3.04  fof(f46,plain,(
% 19.32/3.04    k4_tarski(sK4,sK5) = sK3),
% 19.32/3.04    inference(cnf_transformation,[],[f26])).
% 19.32/3.04  
% 19.32/3.04  fof(f7,axiom,(
% 19.32/3.04    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f41,plain,(
% 19.32/3.04    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 19.32/3.04    inference(cnf_transformation,[],[f7])).
% 19.32/3.04  
% 19.32/3.04  fof(f42,plain,(
% 19.32/3.04    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 19.32/3.04    inference(cnf_transformation,[],[f7])).
% 19.32/3.04  
% 19.32/3.04  fof(f44,plain,(
% 19.32/3.04    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 19.32/3.04    inference(cnf_transformation,[],[f23])).
% 19.32/3.04  
% 19.32/3.04  fof(f1,axiom,(
% 19.32/3.04    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f13,plain,(
% 19.32/3.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.32/3.04    inference(nnf_transformation,[],[f1])).
% 19.32/3.04  
% 19.32/3.04  fof(f14,plain,(
% 19.32/3.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.32/3.04    inference(rectify,[],[f13])).
% 19.32/3.04  
% 19.32/3.04  fof(f15,plain,(
% 19.32/3.04    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 19.32/3.04    introduced(choice_axiom,[])).
% 19.32/3.04  
% 19.32/3.04  fof(f16,plain,(
% 19.32/3.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.32/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 19.32/3.04  
% 19.32/3.04  fof(f27,plain,(
% 19.32/3.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.32/3.04    inference(cnf_transformation,[],[f16])).
% 19.32/3.04  
% 19.32/3.04  fof(f3,axiom,(
% 19.32/3.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f37,plain,(
% 19.32/3.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.32/3.04    inference(cnf_transformation,[],[f3])).
% 19.32/3.04  
% 19.32/3.04  fof(f49,plain,(
% 19.32/3.04    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.32/3.04    inference(definition_unfolding,[],[f37,f48])).
% 19.32/3.04  
% 19.32/3.04  fof(f53,plain,(
% 19.32/3.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.32/3.04    inference(definition_unfolding,[],[f27,f49])).
% 19.32/3.04  
% 19.32/3.04  fof(f63,plain,(
% 19.32/3.04    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 19.32/3.04    inference(equality_resolution,[],[f53])).
% 19.32/3.04  
% 19.32/3.04  fof(f6,axiom,(
% 19.32/3.04    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 19.32/3.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.32/3.04  
% 19.32/3.04  fof(f40,plain,(
% 19.32/3.04    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 19.32/3.04    inference(cnf_transformation,[],[f6])).
% 19.32/3.04  
% 19.32/3.04  fof(f60,plain,(
% 19.32/3.04    ( ! [X0,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0) )),
% 19.32/3.04    inference(definition_unfolding,[],[f40,f49])).
% 19.32/3.04  
% 19.32/3.04  cnf(c_7,plain,
% 19.32/3.04      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 19.32/3.04      inference(cnf_transformation,[],[f65]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113638,plain,
% 19.32/3.04      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_15,plain,
% 19.32/3.04      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 19.32/3.04      inference(cnf_transformation,[],[f43]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113633,plain,
% 19.32/3.04      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_9,plain,
% 19.32/3.04      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 19.32/3.04      inference(cnf_transformation,[],[f68]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113636,plain,
% 19.32/3.04      ( X0 = X1
% 19.32/3.04      | X0 = X2
% 19.32/3.04      | r2_hidden(X0,k2_enumset1(X2,X2,X2,X1)) != iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113948,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,X1)) = X1
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113633,c_113636]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_13,plain,
% 19.32/3.04      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK2(X1) | k1_xboole_0 = X1 ),
% 19.32/3.04      inference(cnf_transformation,[],[f45]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113635,plain,
% 19.32/3.04      ( k4_tarski(X0,X1) != sK2(X2)
% 19.32/3.04      | k1_xboole_0 = X2
% 19.32/3.04      | r2_hidden(X1,X2) != iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114025,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 19.32/3.04      | k4_tarski(X2,X3) != X0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,X1)) = X1
% 19.32/3.04      | r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113948,c_113635]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114958,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X2) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X2)) = X2
% 19.32/3.04      | r2_hidden(X1,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X2)) != iProver_top ),
% 19.32/3.04      inference(equality_resolution,[status(thm)],[c_114025]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116667,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1)) = X1 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113638,c_114958]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_8,plain,
% 19.32/3.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 19.32/3.04      inference(cnf_transformation,[],[f67]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113637,plain,
% 19.32/3.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_16,negated_conjecture,
% 19.32/3.04      ( k1_mcart_1(sK3) = sK3 | k2_mcart_1(sK3) = sK3 ),
% 19.32/3.04      inference(cnf_transformation,[],[f47]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_17,negated_conjecture,
% 19.32/3.04      ( k4_tarski(sK4,sK5) = sK3 ),
% 19.32/3.04      inference(cnf_transformation,[],[f46]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_12,plain,
% 19.32/3.04      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 19.32/3.04      inference(cnf_transformation,[],[f41]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113718,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) = sK4 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_17,c_12]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113726,plain,
% 19.32/3.04      ( k2_mcart_1(sK3) = sK3 | sK4 = sK3 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_16,c_113718]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_11,plain,
% 19.32/3.04      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 19.32/3.04      inference(cnf_transformation,[],[f42]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113710,plain,
% 19.32/3.04      ( k2_mcart_1(sK3) = sK5 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_17,c_11]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113728,plain,
% 19.32/3.04      ( sK5 = sK3 | sK4 = sK3 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_113726,c_113710]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113829,plain,
% 19.32/3.04      ( sK2(X0) != sK3 | k1_xboole_0 = X0 | r2_hidden(sK5,X0) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_17,c_113635]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114022,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,X1)) = X1
% 19.32/3.04      | sK3 != X0
% 19.32/3.04      | r2_hidden(sK5,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113948,c_113829]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114160,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(sK3,sK3,sK3,X0)) = X0
% 19.32/3.04      | r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,X0)) != iProver_top ),
% 19.32/3.04      inference(equality_resolution,[status(thm)],[c_114022]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114359,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(sK3,sK3,sK3,X0)) = X0
% 19.32/3.04      | sK4 = sK3
% 19.32/3.04      | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,X0)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113728,c_114160]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114434,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(sK3,sK3,sK3,X0)) = X0
% 19.32/3.04      | sK4 = sK3 ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_114359,c_113637]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_14,plain,
% 19.32/3.04      ( ~ r2_hidden(X0,X1) | k4_tarski(X0,X2) != sK2(X1) | k1_xboole_0 = X1 ),
% 19.32/3.04      inference(cnf_transformation,[],[f44]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113634,plain,
% 19.32/3.04      ( k4_tarski(X0,X1) != sK2(X2)
% 19.32/3.04      | k1_xboole_0 = X2
% 19.32/3.04      | r2_hidden(X0,X2) != iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114442,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,X0) = k1_xboole_0
% 19.32/3.04      | k4_tarski(X1,X2) != X0
% 19.32/3.04      | sK4 = sK3
% 19.32/3.04      | r2_hidden(X1,k2_enumset1(sK3,sK3,sK3,X0)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_114434,c_113634]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_115485,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,k4_tarski(X0,X1)) = k1_xboole_0
% 19.32/3.04      | sK4 = sK3
% 19.32/3.04      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,k4_tarski(X0,X1))) != iProver_top ),
% 19.32/3.04      inference(equality_resolution,[status(thm)],[c_114442]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_115607,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,k4_tarski(sK3,X0)) = k1_xboole_0 | sK4 = sK3 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113637,c_115485]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_115786,plain,
% 19.32/3.04      ( sK4 = sK3 | r2_hidden(k4_tarski(sK3,X0),k1_xboole_0) = iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_115607,c_113638]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113740,plain,
% 19.32/3.04      ( k4_tarski(sK4,sK3) = sK3 | sK4 = sK3 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113728,c_17]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_3,plain,
% 19.32/3.04      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 19.32/3.04      inference(cnf_transformation,[],[f63]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113639,plain,
% 19.32/3.04      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113777,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113633,c_113639]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113881,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 19.32/3.04      | k4_tarski(X1,X2) != X0
% 19.32/3.04      | r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113777,c_113635]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113971,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k1_xboole_0
% 19.32/3.04      | r2_hidden(X1,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) != iProver_top ),
% 19.32/3.04      inference(equality_resolution,[status(thm)],[c_113881]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114277,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3)) = k1_xboole_0
% 19.32/3.04      | sK4 = sK3
% 19.32/3.04      | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113740,c_113971]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_31,plain,
% 19.32/3.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 19.32/3.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_33,plain,
% 19.32/3.04      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 19.32/3.04      inference(instantiation,[status(thm)],[c_31]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114298,plain,
% 19.32/3.04      ( sK4 = sK3
% 19.32/3.04      | k2_enumset1(k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3)) = k1_xboole_0 ),
% 19.32/3.04      inference(global_propositional_subsumption,[status(thm)],[c_114277,c_33]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114299,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3),k4_tarski(sK4,sK3)) = k1_xboole_0
% 19.32/3.04      | sK4 = sK3 ),
% 19.32/3.04      inference(renaming,[status(thm)],[c_114298]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114314,plain,
% 19.32/3.04      ( k4_tarski(sK4,sK3) = X0
% 19.32/3.04      | sK4 = sK3
% 19.32/3.04      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_114299,c_113636]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_115810,plain,
% 19.32/3.04      ( k4_tarski(sK3,X0) = k4_tarski(sK4,sK3) | sK4 = sK3 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_115786,c_114314]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116137,plain,
% 19.32/3.04      ( k1_mcart_1(k4_tarski(sK3,X0)) = sK4 | sK4 = sK3 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_115810,c_12]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116240,plain,
% 19.32/3.04      ( sK4 = sK3 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_116137,c_12]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_113792,plain,
% 19.32/3.04      ( sK2(X0) != sK3 | k1_xboole_0 = X0 | r2_hidden(sK4,X0) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_17,c_113634]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116295,plain,
% 19.32/3.04      ( sK2(X0) != sK3 | k1_xboole_0 = X0 | r2_hidden(sK3,X0) != iProver_top ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_116240,c_113792]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116709,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1) = k1_xboole_0
% 19.32/3.04      | sK3 != X1
% 19.32/3.04      | r2_hidden(sK3,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),X1)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116667,c_116295]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116802,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(X0,sK3),k4_tarski(X0,sK3),k4_tarski(X0,sK3),sK3) = k1_xboole_0
% 19.32/3.04      | r2_hidden(sK3,k2_enumset1(k4_tarski(X0,sK3),k4_tarski(X0,sK3),k4_tarski(X0,sK3),sK3)) != iProver_top ),
% 19.32/3.04      inference(equality_resolution,[status(thm)],[c_116709]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116813,plain,
% 19.32/3.04      ( k2_enumset1(k4_tarski(X0,sK3),k4_tarski(X0,sK3),k4_tarski(X0,sK3),sK3) = k1_xboole_0 ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_116802,c_113638]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116817,plain,
% 19.32/3.04      ( r2_hidden(k4_tarski(X0,sK3),k1_xboole_0) = iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116813,c_113637]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114030,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,X1)) = X0
% 19.32/3.04      | sK3 != X1
% 19.32/3.04      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113948,c_113792]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114204,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,sK3)) = X0
% 19.32/3.04      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,sK3)) != iProver_top ),
% 19.32/3.04      inference(equality_resolution,[status(thm)],[c_114030]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114423,plain,
% 19.32/3.04      ( k2_enumset1(sK4,sK4,sK4,sK3) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(sK4,sK4,sK4,sK3)) = sK4 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_113637,c_114204]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114684,plain,
% 19.32/3.04      ( k2_enumset1(sK4,sK4,sK4,sK3) = k1_xboole_0
% 19.32/3.04      | sK4 != sK3
% 19.32/3.04      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK3)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_114423,c_113792]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_114761,plain,
% 19.32/3.04      ( k2_enumset1(sK4,sK4,sK4,sK3) = k1_xboole_0 | sK4 != sK3 ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_114684,c_113637]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116280,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 | sK3 != sK3 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_116240,c_114761]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116349,plain,
% 19.32/3.04      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 19.32/3.04      inference(equality_resolution_simp,[status(thm)],[c_116280]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116633,plain,
% 19.32/3.04      ( sK3 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116349,c_113636]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116894,plain,
% 19.32/3.04      ( k4_tarski(X0,sK3) = sK3 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116817,c_116633]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117154,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) = X0 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116894,c_12]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117499,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) != sK3
% 19.32/3.04      | k1_xboole_0 = X0
% 19.32/3.04      | r2_hidden(sK3,X0) != iProver_top ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_117154,c_116295]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117501,plain,
% 19.32/3.04      ( k1_xboole_0 = X0 | r2_hidden(k1_mcart_1(sK3),X0) = iProver_top ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_117154,c_113633]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116297,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) = sK3 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_116240,c_113718]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117569,plain,
% 19.32/3.04      ( k1_xboole_0 = X0 | r2_hidden(sK3,X0) = iProver_top ),
% 19.32/3.04      inference(light_normalisation,[status(thm)],[c_117501,c_116297]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117582,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) != sK3 | k1_xboole_0 = X0 ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_117499,c_117569]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117583,plain,
% 19.32/3.04      ( sK3 != sK3 | k1_xboole_0 = X0 ),
% 19.32/3.04      inference(light_normalisation,[status(thm)],[c_117582,c_116297]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117584,plain,
% 19.32/3.04      ( k1_xboole_0 = X0 ),
% 19.32/3.04      inference(equality_resolution_simp,[status(thm)],[c_117583]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_10,negated_conjecture,
% 19.32/3.04      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 19.32/3.04      inference(cnf_transformation,[],[f60]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116627,plain,
% 19.32/3.04      ( k2_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116349,c_10]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117507,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) != k1_xboole_0 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_117154,c_116627]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117541,plain,
% 19.32/3.04      ( sK3 != k1_xboole_0 ),
% 19.32/3.04      inference(light_normalisation,[status(thm)],[c_117507,c_116297]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116284,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,sK3)) = X0
% 19.32/3.04      | r2_hidden(sK3,k2_enumset1(X0,X0,X0,sK3)) != iProver_top ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_116240,c_114204]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116458,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
% 19.32/3.04      | sK2(k2_enumset1(X0,X0,X0,sK3)) = X0 ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_116284,c_113638]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116462,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0
% 19.32/3.04      | sK3 != X0
% 19.32/3.04      | r2_hidden(sK3,k2_enumset1(X0,X0,X0,sK3)) != iProver_top ),
% 19.32/3.04      inference(superposition,[status(thm)],[c_116458,c_116295]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_116521,plain,
% 19.32/3.04      ( k2_enumset1(X0,X0,X0,sK3) = k1_xboole_0 | sK3 != X0 ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_116462,c_113638]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117511,plain,
% 19.32/3.04      ( k1_mcart_1(sK3) = k1_xboole_0 | sK3 != X0 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_117154,c_116521]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117537,plain,
% 19.32/3.04      ( sK3 != X0 | sK3 = k1_xboole_0 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_117511,c_116297]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117545,plain,
% 19.32/3.04      ( sK3 != X0 ),
% 19.32/3.04      inference(backward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_117541,c_117537]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117588,plain,
% 19.32/3.04      ( k1_xboole_0 != X0 ),
% 19.32/3.04      inference(demodulation,[status(thm)],[c_117584,c_117545]) ).
% 19.32/3.04  
% 19.32/3.04  cnf(c_117591,plain,
% 19.32/3.04      ( $false ),
% 19.32/3.04      inference(forward_subsumption_resolution,
% 19.32/3.04                [status(thm)],
% 19.32/3.04                [c_117588,c_117584]) ).
% 19.32/3.04  
% 19.32/3.04  
% 19.32/3.04  % SZS output end CNFRefutation for theBenchmark.p
% 19.32/3.04  
% 19.32/3.04  ------                               Statistics
% 19.32/3.04  
% 19.32/3.04  ------ Selected
% 19.32/3.04  
% 19.32/3.04  total_time:                             2.02
% 19.32/3.04  
%------------------------------------------------------------------------------
