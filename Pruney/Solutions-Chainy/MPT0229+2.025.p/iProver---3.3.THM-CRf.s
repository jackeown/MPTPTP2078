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
% DateTime   : Thu Dec  3 11:30:40 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 447 expanded)
%              Number of clauses        :   40 (  58 expanded)
%              Number of leaves         :   16 ( 130 expanded)
%              Depth                    :   15
%              Number of atoms          :  297 (1034 expanded)
%              Number of equality atoms :  155 ( 600 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f45,f54,f54])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f28])).

fof(f50,plain,(
    r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f50,f54,f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f54])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f51,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f48,f54,f54,f54])).

fof(f73,plain,(
    ! [X1] : k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f49,f54,f54,f54])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f70,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f58])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_770,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_15523,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k1_xboole_0)
    | X0 != X3
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_15526,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK3,sK3))
    | ~ r2_hidden(sK3,k1_xboole_0)
    | k4_xboole_0(sK3,sK3) != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_15523])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_470,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_472,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1129,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_470,c_472])).

cnf(c_1142,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0
    | r2_hidden(sK1(k4_xboole_0(sK3,sK3)),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_471,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1113,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_470,c_471])).

cnf(c_1124,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0
    | r2_hidden(sK1(k4_xboole_0(sK3,sK3)),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_177,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_178,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(X0,X0,X0,X0,X0) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_603,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_178])).

cnf(c_9,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_467,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_652,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_603,c_467])).

cnf(c_16,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( X0 = X1
    | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_270,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_582,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_583,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_653,plain,
    ( r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_652])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_674,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(X0,X0,X0,X0,X0))
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_676,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_721,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_652,c_16,c_19,c_20,c_583,c_653,c_676])).

cnf(c_726,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_467])).

cnf(c_727,plain,
    ( r2_hidden(sK3,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_726])).

cnf(c_49,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK3,sK3))
    | ~ r2_hidden(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK3,sK3))
    | r2_hidden(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15526,c_1142,c_1124,c_727,c_49,c_46,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:26:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.83/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/0.96  
% 2.83/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.83/0.96  
% 2.83/0.96  ------  iProver source info
% 2.83/0.96  
% 2.83/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.83/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.83/0.96  git: non_committed_changes: false
% 2.83/0.96  git: last_make_outside_of_git: false
% 2.83/0.96  
% 2.83/0.96  ------ 
% 2.83/0.96  ------ Parsing...
% 2.83/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.83/0.96  
% 2.83/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.83/0.96  
% 2.83/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.83/0.96  
% 2.83/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.83/0.96  ------ Proving...
% 2.83/0.96  ------ Problem Properties 
% 2.83/0.96  
% 2.83/0.96  
% 2.83/0.96  clauses                                 15
% 2.83/0.96  conjectures                             1
% 2.83/0.96  EPR                                     1
% 2.83/0.96  Horn                                    7
% 2.83/0.96  unary                                   3
% 2.83/0.96  binary                                  5
% 2.83/0.96  lits                                    35
% 2.83/0.96  lits eq                                 16
% 2.83/0.96  fd_pure                                 0
% 2.83/0.96  fd_pseudo                               0
% 2.83/0.96  fd_cond                                 1
% 2.83/0.96  fd_pseudo_cond                          6
% 2.83/0.96  AC symbols                              0
% 2.83/0.96  
% 2.83/0.96  ------ Input Options Time Limit: Unbounded
% 2.83/0.96  
% 2.83/0.96  
% 2.83/0.96  ------ 
% 2.83/0.96  Current options:
% 2.83/0.96  ------ 
% 2.83/0.96  
% 2.83/0.96  
% 2.83/0.96  
% 2.83/0.96  
% 2.83/0.96  ------ Proving...
% 2.83/0.96  
% 2.83/0.96  
% 2.83/0.96  % SZS status Theorem for theBenchmark.p
% 2.83/0.96  
% 2.83/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.83/0.96  
% 2.83/0.96  fof(f2,axiom,(
% 2.83/0.96    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.83/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.96  
% 2.83/0.96  fof(f12,plain,(
% 2.83/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.83/0.96    inference(ennf_transformation,[],[f2])).
% 2.83/0.96  
% 2.83/0.96  fof(f19,plain,(
% 2.83/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.83/0.96    introduced(choice_axiom,[])).
% 2.83/0.96  
% 2.83/0.96  fof(f20,plain,(
% 2.83/0.96    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.83/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).
% 2.83/0.96  
% 2.83/0.96  fof(f36,plain,(
% 2.83/0.96    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.83/0.96    inference(cnf_transformation,[],[f20])).
% 2.83/0.96  
% 2.83/0.96  fof(f1,axiom,(
% 2.83/0.96    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.83/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.96  
% 2.83/0.96  fof(f14,plain,(
% 2.83/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/0.96    inference(nnf_transformation,[],[f1])).
% 2.83/0.96  
% 2.83/0.96  fof(f15,plain,(
% 2.83/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/0.96    inference(flattening,[],[f14])).
% 2.83/0.96  
% 2.83/0.96  fof(f16,plain,(
% 2.83/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/0.96    inference(rectify,[],[f15])).
% 2.83/0.96  
% 2.83/0.96  fof(f17,plain,(
% 2.83/0.96    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.83/0.96    introduced(choice_axiom,[])).
% 2.83/0.96  
% 2.83/0.96  fof(f18,plain,(
% 2.83/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.83/0.96  
% 2.83/0.96  fof(f31,plain,(
% 2.83/0.96    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.83/0.96    inference(cnf_transformation,[],[f18])).
% 2.83/0.96  
% 2.83/0.96  fof(f66,plain,(
% 2.83/0.96    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.83/0.96    inference(equality_resolution,[],[f31])).
% 2.83/0.96  
% 2.83/0.96  fof(f30,plain,(
% 2.83/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.83/0.96    inference(cnf_transformation,[],[f18])).
% 2.83/0.96  
% 2.83/0.96  fof(f67,plain,(
% 2.83/0.96    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.83/0.96    inference(equality_resolution,[],[f30])).
% 2.83/0.96  
% 2.83/0.96  fof(f8,axiom,(
% 2.83/0.96    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.83/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.96  
% 2.83/0.96  fof(f25,plain,(
% 2.83/0.96    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.83/0.96    inference(nnf_transformation,[],[f8])).
% 2.83/0.96  
% 2.83/0.96  fof(f26,plain,(
% 2.83/0.96    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.83/0.96    inference(flattening,[],[f25])).
% 2.83/0.96  
% 2.83/0.96  fof(f45,plain,(
% 2.83/0.96    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.83/0.96    inference(cnf_transformation,[],[f26])).
% 2.83/0.96  
% 2.83/0.96  fof(f4,axiom,(
% 2.83/0.96    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.83/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.96  
% 2.83/0.96  fof(f41,plain,(
% 2.83/0.96    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.83/0.96    inference(cnf_transformation,[],[f4])).
% 2.83/0.96  
% 2.83/0.96  fof(f5,axiom,(
% 2.83/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.83/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.97  
% 2.83/0.97  fof(f42,plain,(
% 2.83/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.83/0.97    inference(cnf_transformation,[],[f5])).
% 2.83/0.97  
% 2.83/0.97  fof(f6,axiom,(
% 2.83/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.97  
% 2.83/0.97  fof(f43,plain,(
% 2.83/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.83/0.97    inference(cnf_transformation,[],[f6])).
% 2.83/0.97  
% 2.83/0.97  fof(f7,axiom,(
% 2.83/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.97  
% 2.83/0.97  fof(f44,plain,(
% 2.83/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.83/0.97    inference(cnf_transformation,[],[f7])).
% 2.83/0.97  
% 2.83/0.97  fof(f52,plain,(
% 2.83/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.83/0.97    inference(definition_unfolding,[],[f43,f44])).
% 2.83/0.97  
% 2.83/0.97  fof(f53,plain,(
% 2.83/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.83/0.97    inference(definition_unfolding,[],[f42,f52])).
% 2.83/0.97  
% 2.83/0.97  fof(f54,plain,(
% 2.83/0.97    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.83/0.97    inference(definition_unfolding,[],[f41,f53])).
% 2.83/0.97  
% 2.83/0.97  fof(f61,plain,(
% 2.83/0.97    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.83/0.97    inference(definition_unfolding,[],[f45,f54,f54])).
% 2.83/0.97  
% 2.83/0.97  fof(f10,conjecture,(
% 2.83/0.97    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.97  
% 2.83/0.97  fof(f11,negated_conjecture,(
% 2.83/0.97    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.83/0.97    inference(negated_conjecture,[],[f10])).
% 2.83/0.97  
% 2.83/0.97  fof(f13,plain,(
% 2.83/0.97    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.83/0.97    inference(ennf_transformation,[],[f11])).
% 2.83/0.97  
% 2.83/0.97  fof(f28,plain,(
% 2.83/0.97    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 2.83/0.97    introduced(choice_axiom,[])).
% 2.83/0.97  
% 2.83/0.97  fof(f29,plain,(
% 2.83/0.97    sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 2.83/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f28])).
% 2.83/0.97  
% 2.83/0.97  fof(f50,plain,(
% 2.83/0.97    r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 2.83/0.97    inference(cnf_transformation,[],[f29])).
% 2.83/0.97  
% 2.83/0.97  fof(f64,plain,(
% 2.83/0.97    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 2.83/0.97    inference(definition_unfolding,[],[f50,f54,f54])).
% 2.83/0.97  
% 2.83/0.97  fof(f3,axiom,(
% 2.83/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.97  
% 2.83/0.97  fof(f21,plain,(
% 2.83/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.83/0.97    inference(nnf_transformation,[],[f3])).
% 2.83/0.97  
% 2.83/0.97  fof(f22,plain,(
% 2.83/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.83/0.97    inference(rectify,[],[f21])).
% 2.83/0.97  
% 2.83/0.97  fof(f23,plain,(
% 2.83/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.83/0.97    introduced(choice_axiom,[])).
% 2.83/0.97  
% 2.83/0.97  fof(f24,plain,(
% 2.83/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.83/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 2.83/0.97  
% 2.83/0.97  fof(f38,plain,(
% 2.83/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.83/0.97    inference(cnf_transformation,[],[f24])).
% 2.83/0.97  
% 2.83/0.97  fof(f57,plain,(
% 2.83/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.83/0.97    inference(definition_unfolding,[],[f38,f54])).
% 2.83/0.97  
% 2.83/0.97  fof(f68,plain,(
% 2.83/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 2.83/0.97    inference(equality_resolution,[],[f57])).
% 2.83/0.97  
% 2.83/0.97  fof(f69,plain,(
% 2.83/0.97    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 2.83/0.97    inference(equality_resolution,[],[f68])).
% 2.83/0.97  
% 2.83/0.97  fof(f51,plain,(
% 2.83/0.97    sK3 != sK4),
% 2.83/0.97    inference(cnf_transformation,[],[f29])).
% 2.83/0.97  
% 2.83/0.97  fof(f9,axiom,(
% 2.83/0.97    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/0.97  
% 2.83/0.97  fof(f27,plain,(
% 2.83/0.97    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.83/0.97    inference(nnf_transformation,[],[f9])).
% 2.83/0.97  
% 2.83/0.97  fof(f48,plain,(
% 2.83/0.97    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.83/0.97    inference(cnf_transformation,[],[f27])).
% 2.83/0.97  
% 2.83/0.97  fof(f63,plain,(
% 2.83/0.97    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.83/0.97    inference(definition_unfolding,[],[f48,f54,f54,f54])).
% 2.83/0.97  
% 2.83/0.97  fof(f73,plain,(
% 2.83/0.97    ( ! [X1] : (k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 2.83/0.97    inference(equality_resolution,[],[f63])).
% 2.83/0.97  
% 2.83/0.97  fof(f49,plain,(
% 2.83/0.97    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 2.83/0.97    inference(cnf_transformation,[],[f27])).
% 2.83/0.97  
% 2.83/0.97  fof(f62,plain,(
% 2.83/0.97    ( ! [X0,X1] : (k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X0,X0,X0,X0,X0) | X0 = X1) )),
% 2.83/0.97    inference(definition_unfolding,[],[f49,f54,f54,f54])).
% 2.83/0.97  
% 2.83/0.97  fof(f37,plain,(
% 2.83/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.83/0.97    inference(cnf_transformation,[],[f24])).
% 2.83/0.97  
% 2.83/0.97  fof(f58,plain,(
% 2.83/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.83/0.97    inference(definition_unfolding,[],[f37,f54])).
% 2.83/0.97  
% 2.83/0.97  fof(f70,plain,(
% 2.83/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 2.83/0.97    inference(equality_resolution,[],[f58])).
% 2.83/0.97  
% 2.83/0.97  cnf(c_272,plain,
% 2.83/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.83/0.97      theory(equality) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_770,plain,
% 2.83/0.97      ( ~ r2_hidden(X0,X1)
% 2.83/0.97      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 2.83/0.97      | X2 != X0
% 2.83/0.97      | k4_xboole_0(X3,X4) != X1 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_272]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_15523,plain,
% 2.83/0.97      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 2.83/0.97      | ~ r2_hidden(X3,k1_xboole_0)
% 2.83/0.97      | X0 != X3
% 2.83/0.97      | k4_xboole_0(X1,X2) != k1_xboole_0 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_770]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_15526,plain,
% 2.83/0.97      ( r2_hidden(sK3,k4_xboole_0(sK3,sK3))
% 2.83/0.97      | ~ r2_hidden(sK3,k1_xboole_0)
% 2.83/0.97      | k4_xboole_0(sK3,sK3) != k1_xboole_0
% 2.83/0.97      | sK3 != sK3 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_15523]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_6,plain,
% 2.83/0.97      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.83/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_470,plain,
% 2.83/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.83/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_4,plain,
% 2.83/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.83/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_472,plain,
% 2.83/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.83/0.97      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.83/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_1129,plain,
% 2.83/0.97      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.83/0.97      | r2_hidden(sK1(k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 2.83/0.97      inference(superposition,[status(thm)],[c_470,c_472]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_1142,plain,
% 2.83/0.97      ( k4_xboole_0(sK3,sK3) = k1_xboole_0
% 2.83/0.97      | r2_hidden(sK1(k4_xboole_0(sK3,sK3)),sK3) != iProver_top ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_1129]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_5,plain,
% 2.83/0.97      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.83/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_471,plain,
% 2.83/0.97      ( r2_hidden(X0,X1) = iProver_top
% 2.83/0.97      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.83/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_1113,plain,
% 2.83/0.97      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.83/0.97      | r2_hidden(sK1(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 2.83/0.97      inference(superposition,[status(thm)],[c_470,c_471]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_1124,plain,
% 2.83/0.97      ( k4_xboole_0(sK3,sK3) = k1_xboole_0
% 2.83/0.97      | r2_hidden(sK1(k4_xboole_0(sK3,sK3)),sK3) = iProver_top ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_1113]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_13,plain,
% 2.83/0.97      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 2.83/0.97      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.83/0.97      | k1_xboole_0 = X0 ),
% 2.83/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_17,negated_conjecture,
% 2.83/0.97      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 2.83/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_177,plain,
% 2.83/0.97      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.83/0.97      | k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 2.83/0.97      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
% 2.83/0.97      | k1_xboole_0 = X1 ),
% 2.83/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_178,plain,
% 2.83/0.97      ( k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 2.83/0.97      | k3_enumset1(X0,X0,X0,X0,X0) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.83/0.97      | k1_xboole_0 = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.83/0.97      inference(unflattening,[status(thm)],[c_177]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_603,plain,
% 2.83/0.97      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.83/0.97      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.83/0.97      inference(equality_resolution,[status(thm)],[c_178]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_9,plain,
% 2.83/0.97      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 2.83/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_467,plain,
% 2.83/0.97      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.83/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_652,plain,
% 2.83/0.97      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.83/0.97      | r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.83/0.97      inference(superposition,[status(thm)],[c_603,c_467]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_16,negated_conjecture,
% 2.83/0.97      ( sK3 != sK4 ),
% 2.83/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_15,plain,
% 2.83/0.97      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
% 2.83/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_19,plain,
% 2.83/0.97      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_15]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_14,plain,
% 2.83/0.97      ( X0 = X1
% 2.83/0.97      | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 2.83/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_20,plain,
% 2.83/0.97      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.83/0.97      | sK3 = sK3 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_270,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_582,plain,
% 2.83/0.97      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_270]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_583,plain,
% 2.83/0.97      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_582]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_653,plain,
% 2.83/0.97      ( r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.83/0.97      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_652]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_10,plain,
% 2.83/0.97      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.83/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_674,plain,
% 2.83/0.97      ( ~ r2_hidden(sK4,k3_enumset1(X0,X0,X0,X0,X0)) | sK4 = X0 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_676,plain,
% 2.83/0.97      ( ~ r2_hidden(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK4 = sK3 ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_674]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_721,plain,
% 2.83/0.97      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.83/0.97      inference(global_propositional_subsumption,
% 2.83/0.97                [status(thm)],
% 2.83/0.97                [c_652,c_16,c_19,c_20,c_583,c_653,c_676]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_726,plain,
% 2.83/0.97      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 2.83/0.97      inference(superposition,[status(thm)],[c_721,c_467]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_727,plain,
% 2.83/0.97      ( r2_hidden(sK3,k1_xboole_0) ),
% 2.83/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_726]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_49,plain,
% 2.83/0.97      ( ~ r2_hidden(sK3,k4_xboole_0(sK3,sK3)) | ~ r2_hidden(sK3,sK3) ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(c_46,plain,
% 2.83/0.97      ( ~ r2_hidden(sK3,k4_xboole_0(sK3,sK3)) | r2_hidden(sK3,sK3) ),
% 2.83/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 2.83/0.97  
% 2.83/0.97  cnf(contradiction,plain,
% 2.83/0.97      ( $false ),
% 2.83/0.97      inference(minisat,
% 2.83/0.97                [status(thm)],
% 2.83/0.97                [c_15526,c_1142,c_1124,c_727,c_49,c_46,c_20,c_19]) ).
% 2.83/0.97  
% 2.83/0.97  
% 2.83/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.83/0.97  
% 2.83/0.97  ------                               Statistics
% 2.83/0.97  
% 2.83/0.97  ------ Selected
% 2.83/0.97  
% 2.83/0.97  total_time:                             0.428
% 2.83/0.97  
%------------------------------------------------------------------------------
