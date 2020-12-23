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
% DateTime   : Thu Dec  3 11:28:51 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 431 expanded)
%              Number of clauses        :   41 (  79 expanded)
%              Number of leaves         :   17 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  305 (1095 expanded)
%              Number of equality atoms :  128 ( 638 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f31])).

fof(f55,plain,(
    r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f66,plain,(
    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f55,f58,f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f52,f58,f58])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f72,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f56,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_686,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_674,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_675,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1085,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_674,c_675])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_678,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1457,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_678])).

cnf(c_1606,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK1(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4
    | r1_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_1457])).

cnf(c_19,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_827,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_333,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_833,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_942,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | X1 != X0
    | k2_enumset1(X2,X3,X4,X5) != k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1147,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(X0,X0,X0,X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1310,plain,
    ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_331,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1311,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2073,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2079,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1606,c_19,c_827,c_1085,c_1310,c_1311,c_2073])).

cnf(c_679,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2089,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2079,c_679])).

cnf(c_2091,plain,
    ( sK3 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2079,c_678])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_250,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | X3 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_252,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_684,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_683,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_953,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_684,c_683])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_689,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2293,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_689])).

cnf(c_2576,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2091,c_252,c_2293])).

cnf(c_2584,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2089,c_2576])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.61/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.00  
% 1.61/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.61/1.00  
% 1.61/1.00  ------  iProver source info
% 1.61/1.00  
% 1.61/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.61/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.61/1.00  git: non_committed_changes: false
% 1.61/1.00  git: last_make_outside_of_git: false
% 1.61/1.00  
% 1.61/1.00  ------ 
% 1.61/1.00  
% 1.61/1.00  ------ Input Options
% 1.61/1.00  
% 1.61/1.00  --out_options                           all
% 1.61/1.00  --tptp_safe_out                         true
% 1.61/1.00  --problem_path                          ""
% 1.61/1.00  --include_path                          ""
% 1.61/1.00  --clausifier                            res/vclausify_rel
% 1.61/1.00  --clausifier_options                    --mode clausify
% 1.61/1.00  --stdin                                 false
% 1.61/1.00  --stats_out                             all
% 1.61/1.00  
% 1.61/1.00  ------ General Options
% 1.61/1.00  
% 1.61/1.00  --fof                                   false
% 1.61/1.00  --time_out_real                         305.
% 1.61/1.00  --time_out_virtual                      -1.
% 1.61/1.00  --symbol_type_check                     false
% 1.61/1.00  --clausify_out                          false
% 1.61/1.00  --sig_cnt_out                           false
% 1.61/1.00  --trig_cnt_out                          false
% 1.61/1.00  --trig_cnt_out_tolerance                1.
% 1.61/1.00  --trig_cnt_out_sk_spl                   false
% 1.61/1.00  --abstr_cl_out                          false
% 1.61/1.00  
% 1.61/1.00  ------ Global Options
% 1.61/1.00  
% 1.61/1.00  --schedule                              default
% 1.61/1.00  --add_important_lit                     false
% 1.61/1.00  --prop_solver_per_cl                    1000
% 1.61/1.00  --min_unsat_core                        false
% 1.61/1.00  --soft_assumptions                      false
% 1.61/1.00  --soft_lemma_size                       3
% 1.61/1.00  --prop_impl_unit_size                   0
% 1.61/1.00  --prop_impl_unit                        []
% 1.61/1.00  --share_sel_clauses                     true
% 1.61/1.00  --reset_solvers                         false
% 1.61/1.00  --bc_imp_inh                            [conj_cone]
% 1.61/1.00  --conj_cone_tolerance                   3.
% 1.61/1.00  --extra_neg_conj                        none
% 1.61/1.00  --large_theory_mode                     true
% 1.61/1.00  --prolific_symb_bound                   200
% 1.61/1.00  --lt_threshold                          2000
% 1.61/1.00  --clause_weak_htbl                      true
% 1.61/1.00  --gc_record_bc_elim                     false
% 1.61/1.00  
% 1.61/1.00  ------ Preprocessing Options
% 1.61/1.00  
% 1.61/1.00  --preprocessing_flag                    true
% 1.61/1.00  --time_out_prep_mult                    0.1
% 1.61/1.00  --splitting_mode                        input
% 1.61/1.00  --splitting_grd                         true
% 1.61/1.00  --splitting_cvd                         false
% 1.61/1.00  --splitting_cvd_svl                     false
% 1.61/1.00  --splitting_nvd                         32
% 1.61/1.00  --sub_typing                            true
% 1.61/1.00  --prep_gs_sim                           true
% 1.61/1.00  --prep_unflatten                        true
% 1.61/1.00  --prep_res_sim                          true
% 1.61/1.00  --prep_upred                            true
% 1.61/1.00  --prep_sem_filter                       exhaustive
% 1.61/1.00  --prep_sem_filter_out                   false
% 1.61/1.00  --pred_elim                             true
% 1.61/1.00  --res_sim_input                         true
% 1.61/1.00  --eq_ax_congr_red                       true
% 1.61/1.00  --pure_diseq_elim                       true
% 1.61/1.00  --brand_transform                       false
% 1.61/1.00  --non_eq_to_eq                          false
% 1.61/1.00  --prep_def_merge                        true
% 1.61/1.00  --prep_def_merge_prop_impl              false
% 1.77/1.00  --prep_def_merge_mbd                    true
% 1.77/1.00  --prep_def_merge_tr_red                 false
% 1.77/1.00  --prep_def_merge_tr_cl                  false
% 1.77/1.00  --smt_preprocessing                     true
% 1.77/1.00  --smt_ac_axioms                         fast
% 1.77/1.00  --preprocessed_out                      false
% 1.77/1.00  --preprocessed_stats                    false
% 1.77/1.00  
% 1.77/1.00  ------ Abstraction refinement Options
% 1.77/1.00  
% 1.77/1.00  --abstr_ref                             []
% 1.77/1.00  --abstr_ref_prep                        false
% 1.77/1.00  --abstr_ref_until_sat                   false
% 1.77/1.00  --abstr_ref_sig_restrict                funpre
% 1.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.00  --abstr_ref_under                       []
% 1.77/1.00  
% 1.77/1.00  ------ SAT Options
% 1.77/1.00  
% 1.77/1.00  --sat_mode                              false
% 1.77/1.00  --sat_fm_restart_options                ""
% 1.77/1.00  --sat_gr_def                            false
% 1.77/1.00  --sat_epr_types                         true
% 1.77/1.00  --sat_non_cyclic_types                  false
% 1.77/1.00  --sat_finite_models                     false
% 1.77/1.00  --sat_fm_lemmas                         false
% 1.77/1.00  --sat_fm_prep                           false
% 1.77/1.00  --sat_fm_uc_incr                        true
% 1.77/1.00  --sat_out_model                         small
% 1.77/1.00  --sat_out_clauses                       false
% 1.77/1.00  
% 1.77/1.00  ------ QBF Options
% 1.77/1.00  
% 1.77/1.00  --qbf_mode                              false
% 1.77/1.00  --qbf_elim_univ                         false
% 1.77/1.00  --qbf_dom_inst                          none
% 1.77/1.00  --qbf_dom_pre_inst                      false
% 1.77/1.00  --qbf_sk_in                             false
% 1.77/1.00  --qbf_pred_elim                         true
% 1.77/1.00  --qbf_split                             512
% 1.77/1.00  
% 1.77/1.00  ------ BMC1 Options
% 1.77/1.00  
% 1.77/1.00  --bmc1_incremental                      false
% 1.77/1.00  --bmc1_axioms                           reachable_all
% 1.77/1.00  --bmc1_min_bound                        0
% 1.77/1.00  --bmc1_max_bound                        -1
% 1.77/1.00  --bmc1_max_bound_default                -1
% 1.77/1.00  --bmc1_symbol_reachability              true
% 1.77/1.00  --bmc1_property_lemmas                  false
% 1.77/1.00  --bmc1_k_induction                      false
% 1.77/1.00  --bmc1_non_equiv_states                 false
% 1.77/1.00  --bmc1_deadlock                         false
% 1.77/1.00  --bmc1_ucm                              false
% 1.77/1.00  --bmc1_add_unsat_core                   none
% 1.77/1.00  --bmc1_unsat_core_children              false
% 1.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.00  --bmc1_out_stat                         full
% 1.77/1.00  --bmc1_ground_init                      false
% 1.77/1.00  --bmc1_pre_inst_next_state              false
% 1.77/1.00  --bmc1_pre_inst_state                   false
% 1.77/1.00  --bmc1_pre_inst_reach_state             false
% 1.77/1.00  --bmc1_out_unsat_core                   false
% 1.77/1.00  --bmc1_aig_witness_out                  false
% 1.77/1.00  --bmc1_verbose                          false
% 1.77/1.00  --bmc1_dump_clauses_tptp                false
% 1.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.00  --bmc1_dump_file                        -
% 1.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.00  --bmc1_ucm_extend_mode                  1
% 1.77/1.00  --bmc1_ucm_init_mode                    2
% 1.77/1.00  --bmc1_ucm_cone_mode                    none
% 1.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.00  --bmc1_ucm_relax_model                  4
% 1.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.00  --bmc1_ucm_layered_model                none
% 1.77/1.00  --bmc1_ucm_max_lemma_size               10
% 1.77/1.00  
% 1.77/1.00  ------ AIG Options
% 1.77/1.00  
% 1.77/1.00  --aig_mode                              false
% 1.77/1.00  
% 1.77/1.00  ------ Instantiation Options
% 1.77/1.00  
% 1.77/1.00  --instantiation_flag                    true
% 1.77/1.00  --inst_sos_flag                         false
% 1.77/1.00  --inst_sos_phase                        true
% 1.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel_side                     num_symb
% 1.77/1.00  --inst_solver_per_active                1400
% 1.77/1.00  --inst_solver_calls_frac                1.
% 1.77/1.00  --inst_passive_queue_type               priority_queues
% 1.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.00  --inst_passive_queues_freq              [25;2]
% 1.77/1.00  --inst_dismatching                      true
% 1.77/1.00  --inst_eager_unprocessed_to_passive     true
% 1.77/1.00  --inst_prop_sim_given                   true
% 1.77/1.00  --inst_prop_sim_new                     false
% 1.77/1.00  --inst_subs_new                         false
% 1.77/1.00  --inst_eq_res_simp                      false
% 1.77/1.00  --inst_subs_given                       false
% 1.77/1.00  --inst_orphan_elimination               true
% 1.77/1.00  --inst_learning_loop_flag               true
% 1.77/1.00  --inst_learning_start                   3000
% 1.77/1.00  --inst_learning_factor                  2
% 1.77/1.00  --inst_start_prop_sim_after_learn       3
% 1.77/1.00  --inst_sel_renew                        solver
% 1.77/1.00  --inst_lit_activity_flag                true
% 1.77/1.00  --inst_restr_to_given                   false
% 1.77/1.00  --inst_activity_threshold               500
% 1.77/1.00  --inst_out_proof                        true
% 1.77/1.00  
% 1.77/1.00  ------ Resolution Options
% 1.77/1.00  
% 1.77/1.00  --resolution_flag                       true
% 1.77/1.00  --res_lit_sel                           adaptive
% 1.77/1.00  --res_lit_sel_side                      none
% 1.77/1.00  --res_ordering                          kbo
% 1.77/1.00  --res_to_prop_solver                    active
% 1.77/1.00  --res_prop_simpl_new                    false
% 1.77/1.00  --res_prop_simpl_given                  true
% 1.77/1.00  --res_passive_queue_type                priority_queues
% 1.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.00  --res_passive_queues_freq               [15;5]
% 1.77/1.00  --res_forward_subs                      full
% 1.77/1.00  --res_backward_subs                     full
% 1.77/1.00  --res_forward_subs_resolution           true
% 1.77/1.00  --res_backward_subs_resolution          true
% 1.77/1.00  --res_orphan_elimination                true
% 1.77/1.00  --res_time_limit                        2.
% 1.77/1.00  --res_out_proof                         true
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Options
% 1.77/1.00  
% 1.77/1.00  --superposition_flag                    true
% 1.77/1.00  --sup_passive_queue_type                priority_queues
% 1.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.00  --demod_completeness_check              fast
% 1.77/1.00  --demod_use_ground                      true
% 1.77/1.00  --sup_to_prop_solver                    passive
% 1.77/1.00  --sup_prop_simpl_new                    true
% 1.77/1.00  --sup_prop_simpl_given                  true
% 1.77/1.00  --sup_fun_splitting                     false
% 1.77/1.00  --sup_smt_interval                      50000
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Simplification Setup
% 1.77/1.00  
% 1.77/1.00  --sup_indices_passive                   []
% 1.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_full_bw                           [BwDemod]
% 1.77/1.00  --sup_immed_triv                        [TrivRules]
% 1.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_immed_bw_main                     []
% 1.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  
% 1.77/1.00  ------ Combination Options
% 1.77/1.00  
% 1.77/1.00  --comb_res_mult                         3
% 1.77/1.00  --comb_sup_mult                         2
% 1.77/1.00  --comb_inst_mult                        10
% 1.77/1.00  
% 1.77/1.00  ------ Debug Options
% 1.77/1.00  
% 1.77/1.00  --dbg_backtrace                         false
% 1.77/1.00  --dbg_dump_prop_clauses                 false
% 1.77/1.00  --dbg_dump_prop_clauses_file            -
% 1.77/1.00  --dbg_out_stat                          false
% 1.77/1.00  ------ Parsing...
% 1.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.77/1.00  ------ Proving...
% 1.77/1.00  ------ Problem Properties 
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  clauses                                 21
% 1.77/1.00  conjectures                             2
% 1.77/1.00  EPR                                     4
% 1.77/1.00  Horn                                    15
% 1.77/1.00  unary                                   7
% 1.77/1.00  binary                                  6
% 1.77/1.00  lits                                    44
% 1.77/1.00  lits eq                                 12
% 1.77/1.00  fd_pure                                 0
% 1.77/1.00  fd_pseudo                               0
% 1.77/1.00  fd_cond                                 1
% 1.77/1.00  fd_pseudo_cond                          6
% 1.77/1.00  AC symbols                              0
% 1.77/1.00  
% 1.77/1.00  ------ Schedule dynamic 5 is on 
% 1.77/1.00  
% 1.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  ------ 
% 1.77/1.00  Current options:
% 1.77/1.00  ------ 
% 1.77/1.00  
% 1.77/1.00  ------ Input Options
% 1.77/1.00  
% 1.77/1.00  --out_options                           all
% 1.77/1.00  --tptp_safe_out                         true
% 1.77/1.00  --problem_path                          ""
% 1.77/1.00  --include_path                          ""
% 1.77/1.00  --clausifier                            res/vclausify_rel
% 1.77/1.00  --clausifier_options                    --mode clausify
% 1.77/1.00  --stdin                                 false
% 1.77/1.00  --stats_out                             all
% 1.77/1.00  
% 1.77/1.00  ------ General Options
% 1.77/1.00  
% 1.77/1.00  --fof                                   false
% 1.77/1.00  --time_out_real                         305.
% 1.77/1.00  --time_out_virtual                      -1.
% 1.77/1.00  --symbol_type_check                     false
% 1.77/1.00  --clausify_out                          false
% 1.77/1.00  --sig_cnt_out                           false
% 1.77/1.00  --trig_cnt_out                          false
% 1.77/1.00  --trig_cnt_out_tolerance                1.
% 1.77/1.00  --trig_cnt_out_sk_spl                   false
% 1.77/1.00  --abstr_cl_out                          false
% 1.77/1.00  
% 1.77/1.00  ------ Global Options
% 1.77/1.00  
% 1.77/1.00  --schedule                              default
% 1.77/1.00  --add_important_lit                     false
% 1.77/1.00  --prop_solver_per_cl                    1000
% 1.77/1.00  --min_unsat_core                        false
% 1.77/1.00  --soft_assumptions                      false
% 1.77/1.00  --soft_lemma_size                       3
% 1.77/1.00  --prop_impl_unit_size                   0
% 1.77/1.00  --prop_impl_unit                        []
% 1.77/1.00  --share_sel_clauses                     true
% 1.77/1.00  --reset_solvers                         false
% 1.77/1.00  --bc_imp_inh                            [conj_cone]
% 1.77/1.00  --conj_cone_tolerance                   3.
% 1.77/1.00  --extra_neg_conj                        none
% 1.77/1.00  --large_theory_mode                     true
% 1.77/1.00  --prolific_symb_bound                   200
% 1.77/1.00  --lt_threshold                          2000
% 1.77/1.00  --clause_weak_htbl                      true
% 1.77/1.00  --gc_record_bc_elim                     false
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing Options
% 1.77/1.00  
% 1.77/1.00  --preprocessing_flag                    true
% 1.77/1.00  --time_out_prep_mult                    0.1
% 1.77/1.00  --splitting_mode                        input
% 1.77/1.00  --splitting_grd                         true
% 1.77/1.00  --splitting_cvd                         false
% 1.77/1.00  --splitting_cvd_svl                     false
% 1.77/1.00  --splitting_nvd                         32
% 1.77/1.00  --sub_typing                            true
% 1.77/1.00  --prep_gs_sim                           true
% 1.77/1.00  --prep_unflatten                        true
% 1.77/1.00  --prep_res_sim                          true
% 1.77/1.00  --prep_upred                            true
% 1.77/1.00  --prep_sem_filter                       exhaustive
% 1.77/1.00  --prep_sem_filter_out                   false
% 1.77/1.00  --pred_elim                             true
% 1.77/1.00  --res_sim_input                         true
% 1.77/1.00  --eq_ax_congr_red                       true
% 1.77/1.00  --pure_diseq_elim                       true
% 1.77/1.00  --brand_transform                       false
% 1.77/1.00  --non_eq_to_eq                          false
% 1.77/1.00  --prep_def_merge                        true
% 1.77/1.00  --prep_def_merge_prop_impl              false
% 1.77/1.00  --prep_def_merge_mbd                    true
% 1.77/1.00  --prep_def_merge_tr_red                 false
% 1.77/1.00  --prep_def_merge_tr_cl                  false
% 1.77/1.00  --smt_preprocessing                     true
% 1.77/1.00  --smt_ac_axioms                         fast
% 1.77/1.00  --preprocessed_out                      false
% 1.77/1.00  --preprocessed_stats                    false
% 1.77/1.00  
% 1.77/1.00  ------ Abstraction refinement Options
% 1.77/1.00  
% 1.77/1.00  --abstr_ref                             []
% 1.77/1.00  --abstr_ref_prep                        false
% 1.77/1.00  --abstr_ref_until_sat                   false
% 1.77/1.00  --abstr_ref_sig_restrict                funpre
% 1.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.00  --abstr_ref_under                       []
% 1.77/1.00  
% 1.77/1.00  ------ SAT Options
% 1.77/1.00  
% 1.77/1.00  --sat_mode                              false
% 1.77/1.00  --sat_fm_restart_options                ""
% 1.77/1.00  --sat_gr_def                            false
% 1.77/1.00  --sat_epr_types                         true
% 1.77/1.00  --sat_non_cyclic_types                  false
% 1.77/1.00  --sat_finite_models                     false
% 1.77/1.00  --sat_fm_lemmas                         false
% 1.77/1.00  --sat_fm_prep                           false
% 1.77/1.00  --sat_fm_uc_incr                        true
% 1.77/1.00  --sat_out_model                         small
% 1.77/1.00  --sat_out_clauses                       false
% 1.77/1.00  
% 1.77/1.00  ------ QBF Options
% 1.77/1.00  
% 1.77/1.00  --qbf_mode                              false
% 1.77/1.00  --qbf_elim_univ                         false
% 1.77/1.00  --qbf_dom_inst                          none
% 1.77/1.00  --qbf_dom_pre_inst                      false
% 1.77/1.00  --qbf_sk_in                             false
% 1.77/1.00  --qbf_pred_elim                         true
% 1.77/1.00  --qbf_split                             512
% 1.77/1.00  
% 1.77/1.00  ------ BMC1 Options
% 1.77/1.00  
% 1.77/1.00  --bmc1_incremental                      false
% 1.77/1.00  --bmc1_axioms                           reachable_all
% 1.77/1.00  --bmc1_min_bound                        0
% 1.77/1.00  --bmc1_max_bound                        -1
% 1.77/1.00  --bmc1_max_bound_default                -1
% 1.77/1.00  --bmc1_symbol_reachability              true
% 1.77/1.00  --bmc1_property_lemmas                  false
% 1.77/1.00  --bmc1_k_induction                      false
% 1.77/1.00  --bmc1_non_equiv_states                 false
% 1.77/1.00  --bmc1_deadlock                         false
% 1.77/1.00  --bmc1_ucm                              false
% 1.77/1.00  --bmc1_add_unsat_core                   none
% 1.77/1.00  --bmc1_unsat_core_children              false
% 1.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.00  --bmc1_out_stat                         full
% 1.77/1.00  --bmc1_ground_init                      false
% 1.77/1.00  --bmc1_pre_inst_next_state              false
% 1.77/1.00  --bmc1_pre_inst_state                   false
% 1.77/1.00  --bmc1_pre_inst_reach_state             false
% 1.77/1.00  --bmc1_out_unsat_core                   false
% 1.77/1.00  --bmc1_aig_witness_out                  false
% 1.77/1.00  --bmc1_verbose                          false
% 1.77/1.00  --bmc1_dump_clauses_tptp                false
% 1.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.00  --bmc1_dump_file                        -
% 1.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.00  --bmc1_ucm_extend_mode                  1
% 1.77/1.00  --bmc1_ucm_init_mode                    2
% 1.77/1.00  --bmc1_ucm_cone_mode                    none
% 1.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.00  --bmc1_ucm_relax_model                  4
% 1.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.00  --bmc1_ucm_layered_model                none
% 1.77/1.00  --bmc1_ucm_max_lemma_size               10
% 1.77/1.00  
% 1.77/1.00  ------ AIG Options
% 1.77/1.00  
% 1.77/1.00  --aig_mode                              false
% 1.77/1.00  
% 1.77/1.00  ------ Instantiation Options
% 1.77/1.00  
% 1.77/1.00  --instantiation_flag                    true
% 1.77/1.00  --inst_sos_flag                         false
% 1.77/1.00  --inst_sos_phase                        true
% 1.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel_side                     none
% 1.77/1.00  --inst_solver_per_active                1400
% 1.77/1.00  --inst_solver_calls_frac                1.
% 1.77/1.00  --inst_passive_queue_type               priority_queues
% 1.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.00  --inst_passive_queues_freq              [25;2]
% 1.77/1.00  --inst_dismatching                      true
% 1.77/1.00  --inst_eager_unprocessed_to_passive     true
% 1.77/1.00  --inst_prop_sim_given                   true
% 1.77/1.00  --inst_prop_sim_new                     false
% 1.77/1.00  --inst_subs_new                         false
% 1.77/1.00  --inst_eq_res_simp                      false
% 1.77/1.00  --inst_subs_given                       false
% 1.77/1.00  --inst_orphan_elimination               true
% 1.77/1.00  --inst_learning_loop_flag               true
% 1.77/1.00  --inst_learning_start                   3000
% 1.77/1.00  --inst_learning_factor                  2
% 1.77/1.00  --inst_start_prop_sim_after_learn       3
% 1.77/1.00  --inst_sel_renew                        solver
% 1.77/1.00  --inst_lit_activity_flag                true
% 1.77/1.00  --inst_restr_to_given                   false
% 1.77/1.00  --inst_activity_threshold               500
% 1.77/1.00  --inst_out_proof                        true
% 1.77/1.00  
% 1.77/1.00  ------ Resolution Options
% 1.77/1.00  
% 1.77/1.00  --resolution_flag                       false
% 1.77/1.00  --res_lit_sel                           adaptive
% 1.77/1.00  --res_lit_sel_side                      none
% 1.77/1.00  --res_ordering                          kbo
% 1.77/1.00  --res_to_prop_solver                    active
% 1.77/1.00  --res_prop_simpl_new                    false
% 1.77/1.00  --res_prop_simpl_given                  true
% 1.77/1.00  --res_passive_queue_type                priority_queues
% 1.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.00  --res_passive_queues_freq               [15;5]
% 1.77/1.00  --res_forward_subs                      full
% 1.77/1.00  --res_backward_subs                     full
% 1.77/1.00  --res_forward_subs_resolution           true
% 1.77/1.00  --res_backward_subs_resolution          true
% 1.77/1.00  --res_orphan_elimination                true
% 1.77/1.00  --res_time_limit                        2.
% 1.77/1.00  --res_out_proof                         true
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Options
% 1.77/1.00  
% 1.77/1.00  --superposition_flag                    true
% 1.77/1.00  --sup_passive_queue_type                priority_queues
% 1.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.00  --demod_completeness_check              fast
% 1.77/1.00  --demod_use_ground                      true
% 1.77/1.00  --sup_to_prop_solver                    passive
% 1.77/1.00  --sup_prop_simpl_new                    true
% 1.77/1.00  --sup_prop_simpl_given                  true
% 1.77/1.00  --sup_fun_splitting                     false
% 1.77/1.00  --sup_smt_interval                      50000
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Simplification Setup
% 1.77/1.00  
% 1.77/1.00  --sup_indices_passive                   []
% 1.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_full_bw                           [BwDemod]
% 1.77/1.00  --sup_immed_triv                        [TrivRules]
% 1.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_immed_bw_main                     []
% 1.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  
% 1.77/1.00  ------ Combination Options
% 1.77/1.00  
% 1.77/1.00  --comb_res_mult                         3
% 1.77/1.00  --comb_sup_mult                         2
% 1.77/1.00  --comb_inst_mult                        10
% 1.77/1.00  
% 1.77/1.00  ------ Debug Options
% 1.77/1.00  
% 1.77/1.00  --dbg_backtrace                         false
% 1.77/1.00  --dbg_dump_prop_clauses                 false
% 1.77/1.00  --dbg_dump_prop_clauses_file            -
% 1.77/1.00  --dbg_out_stat                          false
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  ------ Proving...
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  % SZS status Theorem for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00   Resolution empty clause
% 1.77/1.00  
% 1.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  fof(f3,axiom,(
% 1.77/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f14,plain,(
% 1.77/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/1.00    inference(rectify,[],[f3])).
% 1.77/1.00  
% 1.77/1.00  fof(f15,plain,(
% 1.77/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.77/1.00    inference(ennf_transformation,[],[f14])).
% 1.77/1.00  
% 1.77/1.00  fof(f23,plain,(
% 1.77/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f24,plain,(
% 1.77/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).
% 1.77/1.00  
% 1.77/1.00  fof(f40,plain,(
% 1.77/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f24])).
% 1.77/1.00  
% 1.77/1.00  fof(f12,conjecture,(
% 1.77/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f13,negated_conjecture,(
% 1.77/1.00    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.77/1.00    inference(negated_conjecture,[],[f12])).
% 1.77/1.00  
% 1.77/1.00  fof(f17,plain,(
% 1.77/1.00    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.77/1.00    inference(ennf_transformation,[],[f13])).
% 1.77/1.00  
% 1.77/1.00  fof(f31,plain,(
% 1.77/1.00    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f32,plain,(
% 1.77/1.00    sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 1.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f31])).
% 1.77/1.00  
% 1.77/1.00  fof(f55,plain,(
% 1.77/1.00    r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 1.77/1.00    inference(cnf_transformation,[],[f32])).
% 1.77/1.00  
% 1.77/1.00  fof(f8,axiom,(
% 1.77/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f49,plain,(
% 1.77/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f8])).
% 1.77/1.00  
% 1.77/1.00  fof(f9,axiom,(
% 1.77/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f50,plain,(
% 1.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f9])).
% 1.77/1.00  
% 1.77/1.00  fof(f10,axiom,(
% 1.77/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f51,plain,(
% 1.77/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f10])).
% 1.77/1.00  
% 1.77/1.00  fof(f57,plain,(
% 1.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.77/1.00    inference(definition_unfolding,[],[f50,f51])).
% 1.77/1.00  
% 1.77/1.00  fof(f58,plain,(
% 1.77/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.77/1.00    inference(definition_unfolding,[],[f49,f57])).
% 1.77/1.00  
% 1.77/1.00  fof(f66,plain,(
% 1.77/1.00    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),
% 1.77/1.00    inference(definition_unfolding,[],[f55,f58,f58])).
% 1.77/1.00  
% 1.77/1.00  fof(f11,axiom,(
% 1.77/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f29,plain,(
% 1.77/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.77/1.00    inference(nnf_transformation,[],[f11])).
% 1.77/1.00  
% 1.77/1.00  fof(f30,plain,(
% 1.77/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.77/1.00    inference(flattening,[],[f29])).
% 1.77/1.00  
% 1.77/1.00  fof(f52,plain,(
% 1.77/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.77/1.00    inference(cnf_transformation,[],[f30])).
% 1.77/1.00  
% 1.77/1.00  fof(f65,plain,(
% 1.77/1.00    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.77/1.00    inference(definition_unfolding,[],[f52,f58,f58])).
% 1.77/1.00  
% 1.77/1.00  fof(f7,axiom,(
% 1.77/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f25,plain,(
% 1.77/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.77/1.00    inference(nnf_transformation,[],[f7])).
% 1.77/1.00  
% 1.77/1.00  fof(f26,plain,(
% 1.77/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.77/1.00    inference(rectify,[],[f25])).
% 1.77/1.00  
% 1.77/1.00  fof(f27,plain,(
% 1.77/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f28,plain,(
% 1.77/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 1.77/1.00  
% 1.77/1.00  fof(f45,plain,(
% 1.77/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.77/1.00    inference(cnf_transformation,[],[f28])).
% 1.77/1.00  
% 1.77/1.00  fof(f62,plain,(
% 1.77/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.77/1.00    inference(definition_unfolding,[],[f45,f58])).
% 1.77/1.00  
% 1.77/1.00  fof(f72,plain,(
% 1.77/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 1.77/1.00    inference(equality_resolution,[],[f62])).
% 1.77/1.00  
% 1.77/1.00  fof(f56,plain,(
% 1.77/1.00    sK3 != sK4),
% 1.77/1.00    inference(cnf_transformation,[],[f32])).
% 1.77/1.00  
% 1.77/1.00  fof(f46,plain,(
% 1.77/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.77/1.00    inference(cnf_transformation,[],[f28])).
% 1.77/1.00  
% 1.77/1.00  fof(f61,plain,(
% 1.77/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.77/1.00    inference(definition_unfolding,[],[f46,f58])).
% 1.77/1.00  
% 1.77/1.00  fof(f70,plain,(
% 1.77/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.77/1.00    inference(equality_resolution,[],[f61])).
% 1.77/1.00  
% 1.77/1.00  fof(f71,plain,(
% 1.77/1.00    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.77/1.00    inference(equality_resolution,[],[f70])).
% 1.77/1.00  
% 1.77/1.00  fof(f41,plain,(
% 1.77/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f24])).
% 1.77/1.00  
% 1.77/1.00  fof(f6,axiom,(
% 1.77/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f44,plain,(
% 1.77/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f6])).
% 1.77/1.00  
% 1.77/1.00  fof(f4,axiom,(
% 1.77/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f42,plain,(
% 1.77/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f4])).
% 1.77/1.00  
% 1.77/1.00  fof(f5,axiom,(
% 1.77/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.01  
% 1.77/1.01  fof(f16,plain,(
% 1.77/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.77/1.01    inference(ennf_transformation,[],[f5])).
% 1.77/1.01  
% 1.77/1.01  fof(f43,plain,(
% 1.77/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.77/1.01    inference(cnf_transformation,[],[f16])).
% 1.77/1.01  
% 1.77/1.01  fof(f2,axiom,(
% 1.77/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.01  
% 1.77/1.01  fof(f18,plain,(
% 1.77/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.77/1.01    inference(nnf_transformation,[],[f2])).
% 1.77/1.01  
% 1.77/1.01  fof(f19,plain,(
% 1.77/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.77/1.01    inference(flattening,[],[f18])).
% 1.77/1.01  
% 1.77/1.01  fof(f20,plain,(
% 1.77/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.77/1.01    inference(rectify,[],[f19])).
% 1.77/1.01  
% 1.77/1.01  fof(f21,plain,(
% 1.77/1.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.77/1.01    introduced(choice_axiom,[])).
% 1.77/1.01  
% 1.77/1.01  fof(f22,plain,(
% 1.77/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.77/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 1.77/1.01  
% 1.77/1.01  fof(f34,plain,(
% 1.77/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.77/1.01    inference(cnf_transformation,[],[f22])).
% 1.77/1.01  
% 1.77/1.01  fof(f68,plain,(
% 1.77/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.77/1.01    inference(equality_resolution,[],[f34])).
% 1.77/1.01  
% 1.77/1.01  cnf(c_7,plain,
% 1.77/1.01      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 1.77/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_686,plain,
% 1.77/1.01      ( r1_xboole_0(X0,X1) = iProver_top
% 1.77/1.01      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_20,negated_conjecture,
% 1.77/1.01      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 1.77/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_674,plain,
% 1.77/1.01      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_18,plain,
% 1.77/1.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 1.77/1.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.77/1.01      | k1_xboole_0 = X0 ),
% 1.77/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_675,plain,
% 1.77/1.01      ( k2_enumset1(X0,X0,X0,X0) = X1
% 1.77/1.01      | k1_xboole_0 = X1
% 1.77/1.01      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_1085,plain,
% 1.77/1.01      ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
% 1.77/1.01      | k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_674,c_675]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_15,plain,
% 1.77/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 1.77/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_678,plain,
% 1.77/1.01      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_1457,plain,
% 1.77/1.01      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 1.77/1.01      | sK4 = X0
% 1.77/1.01      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_1085,c_678]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_1606,plain,
% 1.77/1.01      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 1.77/1.01      | sK1(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4
% 1.77/1.01      | r1_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_686,c_1457]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_19,negated_conjecture,
% 1.77/1.01      ( sK3 != sK4 ),
% 1.77/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_827,plain,
% 1.77/1.01      ( ~ r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | sK3 = sK4 ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_333,plain,
% 1.77/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.77/1.01      theory(equality) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_833,plain,
% 1.77/1.01      ( r2_hidden(X0,X1)
% 1.77/1.01      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
% 1.77/1.01      | X0 != X2
% 1.77/1.01      | X1 != k2_enumset1(X2,X2,X2,X2) ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_333]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_942,plain,
% 1.77/1.01      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 1.77/1.01      | r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
% 1.77/1.01      | X1 != X0
% 1.77/1.01      | k2_enumset1(X2,X3,X4,X5) != k2_enumset1(X0,X0,X0,X0) ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_833]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_1147,plain,
% 1.77/1.01      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 1.77/1.01      | r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 1.77/1.01      | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(X0,X0,X0,X0)
% 1.77/1.01      | sK3 != X0 ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_942]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_1310,plain,
% 1.77/1.01      ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 1.77/1.01      | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.77/1.01      | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK3,sK3,sK3,sK3)
% 1.77/1.01      | sK3 != sK3 ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_1147]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_331,plain,( X0 = X0 ),theory(equality) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_1311,plain,
% 1.77/1.01      ( sK3 = sK3 ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_331]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_14,plain,
% 1.77/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 1.77/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2073,plain,
% 1.77/1.01      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.77/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2079,plain,
% 1.77/1.01      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 1.77/1.01      inference(global_propositional_subsumption,
% 1.77/1.01                [status(thm)],
% 1.77/1.01                [c_1606,c_19,c_827,c_1085,c_1310,c_1311,c_2073]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_679,plain,
% 1.77/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2089,plain,
% 1.77/1.01      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_2079,c_679]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2091,plain,
% 1.77/1.01      ( sK3 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_2079,c_678]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_6,plain,
% 1.77/1.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 1.77/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_11,plain,
% 1.77/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.77/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_250,plain,
% 1.77/1.01      ( ~ r2_hidden(X0,X1)
% 1.77/1.01      | ~ r2_hidden(X0,X2)
% 1.77/1.01      | X3 != X2
% 1.77/1.01      | k1_xboole_0 != X1 ),
% 1.77/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_251,plain,
% 1.77/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 1.77/1.01      inference(unflattening,[status(thm)],[c_250]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_252,plain,
% 1.77/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.77/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_9,plain,
% 1.77/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 1.77/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_684,plain,
% 1.77/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_10,plain,
% 1.77/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.77/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_683,plain,
% 1.77/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_953,plain,
% 1.77/1.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_684,c_683]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_4,plain,
% 1.77/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 1.77/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_689,plain,
% 1.77/1.01      ( r2_hidden(X0,X1) = iProver_top
% 1.77/1.01      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 1.77/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2293,plain,
% 1.77/1.01      ( r2_hidden(X0,X1) = iProver_top
% 1.77/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_953,c_689]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2576,plain,
% 1.77/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.77/1.01      inference(global_propositional_subsumption,
% 1.77/1.01                [status(thm)],
% 1.77/1.01                [c_2091,c_252,c_2293]) ).
% 1.77/1.01  
% 1.77/1.01  cnf(c_2584,plain,
% 1.77/1.01      ( $false ),
% 1.77/1.01      inference(superposition,[status(thm)],[c_2089,c_2576]) ).
% 1.77/1.01  
% 1.77/1.01  
% 1.77/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.77/1.01  
% 1.77/1.01  ------                               Statistics
% 1.77/1.01  
% 1.77/1.01  ------ General
% 1.77/1.01  
% 1.77/1.01  abstr_ref_over_cycles:                  0
% 1.77/1.01  abstr_ref_under_cycles:                 0
% 1.77/1.01  gc_basic_clause_elim:                   0
% 1.77/1.01  forced_gc_time:                         0
% 1.77/1.01  parsing_time:                           0.012
% 1.77/1.01  unif_index_cands_time:                  0.
% 1.77/1.01  unif_index_add_time:                    0.
% 1.77/1.01  orderings_time:                         0.
% 1.77/1.01  out_proof_time:                         0.017
% 1.77/1.01  total_time:                             0.126
% 1.77/1.01  num_of_symbols:                         42
% 1.77/1.01  num_of_terms:                           3144
% 1.77/1.01  
% 1.77/1.01  ------ Preprocessing
% 1.77/1.01  
% 1.77/1.01  num_of_splits:                          0
% 1.77/1.01  num_of_split_atoms:                     0
% 1.77/1.01  num_of_reused_defs:                     0
% 1.77/1.01  num_eq_ax_congr_red:                    20
% 1.77/1.01  num_of_sem_filtered_clauses:            1
% 1.77/1.01  num_of_subtypes:                        0
% 1.77/1.01  monotx_restored_types:                  0
% 1.77/1.01  sat_num_of_epr_types:                   0
% 1.77/1.01  sat_num_of_non_cyclic_types:            0
% 1.77/1.01  sat_guarded_non_collapsed_types:        0
% 1.77/1.01  num_pure_diseq_elim:                    0
% 1.77/1.01  simp_replaced_by:                       0
% 1.77/1.01  res_preprocessed:                       76
% 1.77/1.01  prep_upred:                             0
% 1.77/1.01  prep_unflattend:                        12
% 1.77/1.01  smt_new_axioms:                         0
% 1.77/1.01  pred_elim_cands:                        3
% 1.77/1.01  pred_elim:                              0
% 1.77/1.01  pred_elim_cl:                           0
% 1.77/1.01  pred_elim_cycles:                       2
% 1.77/1.01  merged_defs:                            0
% 1.77/1.01  merged_defs_ncl:                        0
% 1.77/1.01  bin_hyper_res:                          0
% 1.77/1.01  prep_cycles:                            3
% 1.77/1.01  pred_elim_time:                         0.001
% 1.77/1.01  splitting_time:                         0.
% 1.77/1.01  sem_filter_time:                        0.
% 1.77/1.01  monotx_time:                            0.
% 1.77/1.01  subtype_inf_time:                       0.
% 1.77/1.01  
% 1.77/1.01  ------ Problem properties
% 1.77/1.01  
% 1.77/1.01  clauses:                                21
% 1.77/1.01  conjectures:                            2
% 1.77/1.01  epr:                                    4
% 1.77/1.01  horn:                                   15
% 1.77/1.01  ground:                                 2
% 1.77/1.01  unary:                                  7
% 1.77/1.01  binary:                                 6
% 1.77/1.01  lits:                                   44
% 1.77/1.01  lits_eq:                                12
% 1.77/1.01  fd_pure:                                0
% 1.77/1.01  fd_pseudo:                              0
% 1.77/1.01  fd_cond:                                1
% 1.77/1.01  fd_pseudo_cond:                         6
% 1.77/1.01  ac_symbols:                             0
% 1.77/1.01  
% 1.77/1.01  ------ Propositional Solver
% 1.77/1.01  
% 1.77/1.01  prop_solver_calls:                      22
% 1.77/1.01  prop_fast_solver_calls:                 417
% 1.77/1.01  smt_solver_calls:                       0
% 1.77/1.01  smt_fast_solver_calls:                  0
% 1.77/1.01  prop_num_of_clauses:                    986
% 1.77/1.01  prop_preprocess_simplified:             4267
% 1.77/1.01  prop_fo_subsumed:                       3
% 1.77/1.01  prop_solver_time:                       0.
% 1.77/1.01  smt_solver_time:                        0.
% 1.77/1.01  smt_fast_solver_time:                   0.
% 1.77/1.01  prop_fast_solver_time:                  0.
% 1.77/1.01  prop_unsat_core_time:                   0.
% 1.77/1.01  
% 1.77/1.01  ------ QBF
% 1.77/1.01  
% 1.77/1.01  qbf_q_res:                              0
% 1.77/1.01  qbf_num_tautologies:                    0
% 1.77/1.01  qbf_prep_cycles:                        0
% 1.77/1.01  
% 1.77/1.01  ------ BMC1
% 1.77/1.01  
% 1.77/1.01  bmc1_current_bound:                     -1
% 1.77/1.01  bmc1_last_solved_bound:                 -1
% 1.77/1.01  bmc1_unsat_core_size:                   -1
% 1.77/1.01  bmc1_unsat_core_parents_size:           -1
% 1.77/1.01  bmc1_merge_next_fun:                    0
% 1.77/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.77/1.01  
% 1.77/1.01  ------ Instantiation
% 1.77/1.01  
% 1.77/1.01  inst_num_of_clauses:                    317
% 1.77/1.01  inst_num_in_passive:                    116
% 1.77/1.01  inst_num_in_active:                     120
% 1.77/1.01  inst_num_in_unprocessed:                81
% 1.77/1.01  inst_num_of_loops:                      130
% 1.77/1.01  inst_num_of_learning_restarts:          0
% 1.77/1.01  inst_num_moves_active_passive:          8
% 1.77/1.01  inst_lit_activity:                      0
% 1.77/1.01  inst_lit_activity_moves:                0
% 1.77/1.01  inst_num_tautologies:                   0
% 1.77/1.01  inst_num_prop_implied:                  0
% 1.77/1.01  inst_num_existing_simplified:           0
% 1.77/1.01  inst_num_eq_res_simplified:             0
% 1.77/1.01  inst_num_child_elim:                    0
% 1.77/1.01  inst_num_of_dismatching_blockings:      97
% 1.77/1.01  inst_num_of_non_proper_insts:           259
% 1.77/1.01  inst_num_of_duplicates:                 0
% 1.77/1.01  inst_inst_num_from_inst_to_res:         0
% 1.77/1.01  inst_dismatching_checking_time:         0.
% 1.77/1.01  
% 1.77/1.01  ------ Resolution
% 1.77/1.01  
% 1.77/1.01  res_num_of_clauses:                     0
% 1.77/1.01  res_num_in_passive:                     0
% 1.77/1.01  res_num_in_active:                      0
% 1.77/1.01  res_num_of_loops:                       79
% 1.77/1.01  res_forward_subset_subsumed:            22
% 1.77/1.01  res_backward_subset_subsumed:           0
% 1.77/1.01  res_forward_subsumed:                   0
% 1.77/1.01  res_backward_subsumed:                  0
% 1.77/1.01  res_forward_subsumption_resolution:     0
% 1.77/1.01  res_backward_subsumption_resolution:    0
% 1.77/1.01  res_clause_to_clause_subsumption:       94
% 1.77/1.01  res_orphan_elimination:                 0
% 1.77/1.01  res_tautology_del:                      9
% 1.77/1.01  res_num_eq_res_simplified:              0
% 1.77/1.01  res_num_sel_changes:                    0
% 1.77/1.01  res_moves_from_active_to_pass:          0
% 1.77/1.01  
% 1.77/1.01  ------ Superposition
% 1.77/1.01  
% 1.77/1.01  sup_time_total:                         0.
% 1.77/1.01  sup_time_generating:                    0.
% 1.77/1.01  sup_time_sim_full:                      0.
% 1.77/1.01  sup_time_sim_immed:                     0.
% 1.77/1.01  
% 1.77/1.01  sup_num_of_clauses:                     40
% 1.77/1.01  sup_num_in_active:                      20
% 1.77/1.01  sup_num_in_passive:                     20
% 1.77/1.01  sup_num_of_loops:                       25
% 1.77/1.01  sup_fw_superposition:                   27
% 1.77/1.01  sup_bw_superposition:                   29
% 1.77/1.01  sup_immediate_simplified:               10
% 1.77/1.01  sup_given_eliminated:                   0
% 1.77/1.01  comparisons_done:                       0
% 1.77/1.01  comparisons_avoided:                    5
% 1.77/1.01  
% 1.77/1.01  ------ Simplifications
% 1.77/1.01  
% 1.77/1.01  
% 1.77/1.01  sim_fw_subset_subsumed:                 5
% 1.77/1.01  sim_bw_subset_subsumed:                 5
% 1.77/1.01  sim_fw_subsumed:                        5
% 1.77/1.01  sim_bw_subsumed:                        0
% 1.77/1.01  sim_fw_subsumption_res:                 0
% 1.77/1.01  sim_bw_subsumption_res:                 0
% 1.77/1.01  sim_tautology_del:                      4
% 1.77/1.01  sim_eq_tautology_del:                   6
% 1.77/1.01  sim_eq_res_simp:                        0
% 1.77/1.01  sim_fw_demodulated:                     0
% 1.77/1.01  sim_bw_demodulated:                     3
% 1.77/1.01  sim_light_normalised:                   0
% 1.77/1.01  sim_joinable_taut:                      0
% 1.77/1.01  sim_joinable_simp:                      0
% 1.77/1.01  sim_ac_normalised:                      0
% 1.77/1.01  sim_smt_subsumption:                    0
% 1.77/1.01  
%------------------------------------------------------------------------------
