%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:26 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  102 (1466 expanded)
%              Number of clauses        :   54 ( 414 expanded)
%              Number of leaves         :    9 ( 296 expanded)
%              Depth                    :   26
%              Number of atoms          :  363 (8997 expanded)
%              Number of equality atoms :  197 (3064 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f54,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f55,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK2,sK4)
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0 )
      & ( ( r2_hidden(sK3,sK4)
          & r2_hidden(sK2,sK4) )
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0 )
    & ( ( r2_hidden(sK3,sK4)
        & r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f21])).

fof(f37,plain,
    ( r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,
    ( r2_hidden(sK2,sK4)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f38,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f52,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f53,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f52])).

fof(f39,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f39,f36])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10957,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10953,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10965,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10963,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11106,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_10963])).

cnf(c_6146,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6149,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6233,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_6149])).

cnf(c_6274,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6146,c_6233])).

cnf(c_11109,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11106,c_6274])).

cnf(c_11153,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10965,c_11109])).

cnf(c_11163,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11153,c_6])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10962,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11237,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X2,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11163,c_10962])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10956,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12867,plain,
    ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = X1
    | sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = X2
    | k4_xboole_0(k1_enumset1(X1,X1,X2),X3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11237,c_10956])).

cnf(c_11238,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X2,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11163,c_10963])).

cnf(c_23754,plain,
    ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = X1
    | k4_xboole_0(k1_enumset1(X1,X1,X2),X3) = k1_xboole_0
    | r2_hidden(X2,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12867,c_11238])).

cnf(c_24174,plain,
    ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,sK2),sK4)) = X1
    | k4_xboole_0(k1_enumset1(X1,X1,sK2),sK4) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10953,c_23754])).

cnf(c_16,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10954,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24173,plain,
    ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,sK3),sK4)) = X1
    | k4_xboole_0(k1_enumset1(X1,X1,sK3),sK4) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10954,c_23754])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10966,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11620,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10965,c_10966])).

cnf(c_12220,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11620,c_10963])).

cnf(c_12222,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11620,c_11109])).

cnf(c_12303,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(X2,X2,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12220,c_12222])).

cnf(c_24670,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,sK3),sK4) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24173,c_12303])).

cnf(c_24725,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24670])).

cnf(c_24737,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24174,c_16,c_24725])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10964,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_24853,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24737,c_10964])).

cnf(c_25457,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24853,c_6274])).

cnf(c_25458,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_25457])).

cnf(c_25469,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10957,c_25458])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10958,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_25468,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10958,c_25458])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10955,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) != k1_xboole_0
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_24740,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24737,c_10955])).

cnf(c_162,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_822,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25469,c_25468,c_24740,c_822])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.63/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.49  
% 7.63/1.49  ------  iProver source info
% 7.63/1.49  
% 7.63/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.49  git: non_committed_changes: false
% 7.63/1.49  git: last_make_outside_of_git: false
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  ------ Parsing...
% 7.63/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  ------ Proving...
% 7.63/1.49  ------ Problem Properties 
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  clauses                                 16
% 7.63/1.49  conjectures                             4
% 7.63/1.49  EPR                                     0
% 7.63/1.49  Horn                                    8
% 7.63/1.49  unary                                   3
% 7.63/1.49  binary                                  4
% 7.63/1.49  lits                                    40
% 7.63/1.49  lits eq                                 16
% 7.63/1.49  fd_pure                                 0
% 7.63/1.49  fd_pseudo                               0
% 7.63/1.49  fd_cond                                 0
% 7.63/1.49  fd_pseudo_cond                          6
% 7.63/1.49  AC symbols                              0
% 7.63/1.49  
% 7.63/1.49  ------ Input Options Time Limit: Unbounded
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.63/1.49  Current options:
% 7.63/1.49  ------ 
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS status Theorem for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  fof(f4,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f14,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.63/1.49    inference(nnf_transformation,[],[f4])).
% 7.63/1.49  
% 7.63/1.49  fof(f15,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.63/1.49    inference(flattening,[],[f14])).
% 7.63/1.49  
% 7.63/1.49  fof(f16,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.63/1.49    inference(rectify,[],[f15])).
% 7.63/1.49  
% 7.63/1.49  fof(f17,plain,(
% 7.63/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f18,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 7.63/1.49  
% 7.63/1.49  fof(f31,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.63/1.49    inference(cnf_transformation,[],[f18])).
% 7.63/1.49  
% 7.63/1.49  fof(f5,axiom,(
% 7.63/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f36,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f5])).
% 7.63/1.49  
% 7.63/1.49  fof(f44,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.63/1.49    inference(definition_unfolding,[],[f31,f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f54,plain,(
% 7.63/1.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 7.63/1.49    inference(equality_resolution,[],[f44])).
% 7.63/1.49  
% 7.63/1.49  fof(f55,plain,(
% 7.63/1.49    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 7.63/1.49    inference(equality_resolution,[],[f54])).
% 7.63/1.49  
% 7.63/1.49  fof(f6,conjecture,(
% 7.63/1.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f7,negated_conjecture,(
% 7.63/1.49    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.63/1.49    inference(negated_conjecture,[],[f6])).
% 7.63/1.49  
% 7.63/1.49  fof(f8,plain,(
% 7.63/1.49    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.63/1.49    inference(ennf_transformation,[],[f7])).
% 7.63/1.49  
% 7.63/1.49  fof(f19,plain,(
% 7.63/1.49    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 7.63/1.49    inference(nnf_transformation,[],[f8])).
% 7.63/1.49  
% 7.63/1.49  fof(f20,plain,(
% 7.63/1.49    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 7.63/1.49    inference(flattening,[],[f19])).
% 7.63/1.49  
% 7.63/1.49  fof(f21,plain,(
% 7.63/1.49    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0)) => ((~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f22,plain,(
% 7.63/1.49    (~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0)),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f21])).
% 7.63/1.49  
% 7.63/1.49  fof(f37,plain,(
% 7.63/1.49    r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f48,plain,(
% 7.63/1.49    r2_hidden(sK2,sK4) | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0),
% 7.63/1.49    inference(definition_unfolding,[],[f37,f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f1,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f9,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.63/1.49    inference(nnf_transformation,[],[f1])).
% 7.63/1.49  
% 7.63/1.49  fof(f10,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.63/1.49    inference(flattening,[],[f9])).
% 7.63/1.49  
% 7.63/1.49  fof(f11,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.63/1.49    inference(rectify,[],[f10])).
% 7.63/1.49  
% 7.63/1.49  fof(f12,plain,(
% 7.63/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f13,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 7.63/1.49  
% 7.63/1.49  fof(f26,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f3,axiom,(
% 7.63/1.49    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f29,plain,(
% 7.63/1.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.63/1.49    inference(cnf_transformation,[],[f3])).
% 7.63/1.49  
% 7.63/1.49  fof(f24,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.63/1.49    inference(cnf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f50,plain,(
% 7.63/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.63/1.49    inference(equality_resolution,[],[f24])).
% 7.63/1.49  
% 7.63/1.49  fof(f23,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.63/1.49    inference(cnf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f51,plain,(
% 7.63/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.63/1.49    inference(equality_resolution,[],[f23])).
% 7.63/1.49  
% 7.63/1.49  fof(f30,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.63/1.49    inference(cnf_transformation,[],[f18])).
% 7.63/1.49  
% 7.63/1.49  fof(f45,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 7.63/1.49    inference(definition_unfolding,[],[f30,f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f56,plain,(
% 7.63/1.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 7.63/1.49    inference(equality_resolution,[],[f45])).
% 7.63/1.49  
% 7.63/1.49  fof(f38,plain,(
% 7.63/1.49    r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f47,plain,(
% 7.63/1.49    r2_hidden(sK3,sK4) | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0),
% 7.63/1.49    inference(definition_unfolding,[],[f38,f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f27,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f25,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.63/1.49    inference(cnf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f49,plain,(
% 7.63/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.63/1.49    inference(equality_resolution,[],[f25])).
% 7.63/1.49  
% 7.63/1.49  fof(f32,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.63/1.49    inference(cnf_transformation,[],[f18])).
% 7.63/1.49  
% 7.63/1.49  fof(f43,plain,(
% 7.63/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.63/1.49    inference(definition_unfolding,[],[f32,f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f52,plain,(
% 7.63/1.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 7.63/1.49    inference(equality_resolution,[],[f43])).
% 7.63/1.49  
% 7.63/1.49  fof(f53,plain,(
% 7.63/1.49    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 7.63/1.49    inference(equality_resolution,[],[f52])).
% 7.63/1.49  
% 7.63/1.49  fof(f39,plain,(
% 7.63/1.49    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f46,plain,(
% 7.63/1.49    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) != k1_xboole_0),
% 7.63/1.49    inference(definition_unfolding,[],[f39,f36])).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10957,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_15,negated_conjecture,
% 7.63/1.49      ( r2_hidden(sK2,sK4)
% 7.63/1.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10953,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK2,sK4) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2,plain,
% 7.63/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.63/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.63/1.49      | k4_xboole_0(X0,X1) = X2 ),
% 7.63/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10965,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X1) = X2
% 7.63/1.49      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.63/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6,plain,
% 7.63/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_4,negated_conjecture,
% 7.63/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10963,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11106,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_6,c_10963]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6146,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6149,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6233,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_6,c_6149]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6274,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_6146,c_6233]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11109,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_11106,c_6274]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11153,plain,
% 7.63/1.49      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 7.63/1.49      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_10965,c_11109]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11163,plain,
% 7.63/1.49      ( k1_xboole_0 = X0
% 7.63/1.49      | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_11153,c_6]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_5,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10962,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.63/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11237,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK0(k1_xboole_0,X2,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_11163,c_10962]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12,plain,
% 7.63/1.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.63/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10956,plain,
% 7.63/1.49      ( X0 = X1
% 7.63/1.49      | X0 = X2
% 7.63/1.49      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12867,plain,
% 7.63/1.49      ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = X1
% 7.63/1.49      | sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = X2
% 7.63/1.49      | k4_xboole_0(k1_enumset1(X1,X1,X2),X3) = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_11237,c_10956]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11238,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK0(k1_xboole_0,X2,k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_11163,c_10963]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_23754,plain,
% 7.63/1.49      ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = X1
% 7.63/1.49      | k4_xboole_0(k1_enumset1(X1,X1,X2),X3) = k1_xboole_0
% 7.63/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_12867,c_11238]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24174,plain,
% 7.63/1.49      ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,sK2),sK4)) = X1
% 7.63/1.49      | k4_xboole_0(k1_enumset1(X1,X1,sK2),sK4) = k1_xboole_0
% 7.63/1.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_10953,c_23754]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_16,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK2,sK4) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_14,negated_conjecture,
% 7.63/1.49      ( r2_hidden(sK3,sK4)
% 7.63/1.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10954,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24173,plain,
% 7.63/1.49      ( sK0(k1_xboole_0,X0,k4_xboole_0(k1_enumset1(X1,X1,sK3),sK4)) = X1
% 7.63/1.49      | k4_xboole_0(k1_enumset1(X1,X1,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_10954,c_23754]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1,plain,
% 7.63/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.63/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.63/1.49      | k4_xboole_0(X0,X1) = X2 ),
% 7.63/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10966,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X1) = X2
% 7.63/1.49      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 7.63/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11620,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X0) = X1
% 7.63/1.49      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_10965,c_10966]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12220,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 7.63/1.49      | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_11620,c_10963]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12222,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_11620,c_11109]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12303,plain,
% 7.63/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK0(X2,X2,k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 7.63/1.49      inference(light_normalisation,[status(thm)],[c_12220,c_12222]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24670,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(X0,X0,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_24173,c_12303]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24725,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0
% 7.63/1.49      | r2_hidden(sK2,sK4) != iProver_top ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_24670]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24737,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = k1_xboole_0 ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_24174,c_16,c_24725]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3,plain,
% 7.63/1.49      ( ~ r2_hidden(X0,X1)
% 7.63/1.49      | r2_hidden(X0,X2)
% 7.63/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10964,plain,
% 7.63/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.63/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24853,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 7.63/1.49      | r2_hidden(X0,sK4) = iProver_top
% 7.63/1.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_24737,c_10964]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_25457,plain,
% 7.63/1.49      ( r2_hidden(X0,sK4) = iProver_top
% 7.63/1.49      | r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_24853,c_6274]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_25458,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 7.63/1.49      | r2_hidden(X0,sK4) = iProver_top ),
% 7.63/1.49      inference(renaming,[status(thm)],[c_25457]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_25469,plain,
% 7.63/1.49      ( r2_hidden(sK2,sK4) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_10957,c_25458]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10958,plain,
% 7.63/1.49      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_25468,plain,
% 7.63/1.49      ( r2_hidden(sK3,sK4) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_10958,c_25458]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_13,negated_conjecture,
% 7.63/1.49      ( ~ r2_hidden(sK2,sK4)
% 7.63/1.49      | ~ r2_hidden(sK3,sK4)
% 7.63/1.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) != k1_xboole_0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10955,plain,
% 7.63/1.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) != k1_xboole_0
% 7.63/1.49      | r2_hidden(sK2,sK4) != iProver_top
% 7.63/1.49      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24740,plain,
% 7.63/1.49      ( k1_xboole_0 != k1_xboole_0
% 7.63/1.49      | r2_hidden(sK2,sK4) != iProver_top
% 7.63/1.49      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_24737,c_10955]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_162,plain,( X0 = X0 ),theory(equality) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_822,plain,
% 7.63/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_162]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(contradiction,plain,
% 7.63/1.49      ( $false ),
% 7.63/1.49      inference(minisat,[status(thm)],[c_25469,c_25468,c_24740,c_822]) ).
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  ------                               Statistics
% 7.63/1.49  
% 7.63/1.49  ------ Selected
% 7.63/1.49  
% 7.63/1.49  total_time:                             0.562
% 7.63/1.49  
%------------------------------------------------------------------------------
