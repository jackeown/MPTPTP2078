%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:05 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 924 expanded)
%              Number of clauses        :   45 ( 138 expanded)
%              Number of leaves         :   19 ( 284 expanded)
%              Depth                    :   17
%              Number of atoms          :  261 (1381 expanded)
%              Number of equality atoms :  108 ( 918 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f40])).

fof(f71,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f76])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f73,f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f63,f75,f75])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f60,f73,f73,f57])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) != sK4 ),
    inference(definition_unfolding,[],[f72,f73,f76])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_995,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_997,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_999,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2202,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_999])).

cnf(c_5378,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_995,c_2202])).

cnf(c_22,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5428,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_5378,c_22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1012,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1346,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_19,c_22])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1350,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_22,c_15])).

cnf(c_1918,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1346,c_1350])).

cnf(c_17,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2026,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1918,c_17])).

cnf(c_2028,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2026,c_1918])).

cnf(c_2030,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2028,c_1918])).

cnf(c_2166,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2030,c_15])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1006,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3356,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_1006])).

cnf(c_4053,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_3356])).

cnf(c_4086,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4053,c_999])).

cnf(c_4197,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_4086,c_2166])).

cnf(c_14,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1000,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1220,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1000,c_999])).

cnf(c_3357,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1006])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1005,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3093,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1005])).

cnf(c_4744,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3357,c_3093])).

cnf(c_4751,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_4744])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1001,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4085,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_1001])).

cnf(c_4789,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4751,c_4085])).

cnf(c_5430,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
    inference(demodulation,[status(thm)],[c_5428,c_4197,c_4789])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) != sK4 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1908,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
    inference(demodulation,[status(thm)],[c_1346,c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5430,c_1908])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     num_symb
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       true
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 24
% 2.78/1.00  conjectures                             2
% 2.78/1.00  EPR                                     6
% 2.78/1.00  Horn                                    17
% 2.78/1.00  unary                                   8
% 2.78/1.00  binary                                  9
% 2.78/1.00  lits                                    48
% 2.78/1.00  lits eq                                 10
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 0
% 2.78/1.00  fd_pseudo_cond                          4
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Schedule dynamic 5 is on 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     none
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       false
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ Proving...
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS status Theorem for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  fof(f19,conjecture,(
% 2.78/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f20,negated_conjecture,(
% 2.78/1.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.78/1.00    inference(negated_conjecture,[],[f19])).
% 2.78/1.00  
% 2.78/1.00  fof(f25,plain,(
% 2.78/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 2.78/1.00    inference(ennf_transformation,[],[f20])).
% 2.78/1.00  
% 2.78/1.00  fof(f40,plain,(
% 2.78/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f41,plain,(
% 2.78/1.00    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f40])).
% 2.78/1.00  
% 2.78/1.00  fof(f71,plain,(
% 2.78/1.00    r2_hidden(sK3,sK4)),
% 2.78/1.00    inference(cnf_transformation,[],[f41])).
% 2.78/1.00  
% 2.78/1.00  fof(f17,axiom,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f39,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.78/1.00    inference(nnf_transformation,[],[f17])).
% 2.78/1.00  
% 2.78/1.00  fof(f69,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f13,axiom,(
% 2.78/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f64,plain,(
% 2.78/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f13])).
% 2.78/1.00  
% 2.78/1.00  fof(f14,axiom,(
% 2.78/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f65,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f14])).
% 2.78/1.00  
% 2.78/1.00  fof(f15,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f66,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f15])).
% 2.78/1.00  
% 2.78/1.00  fof(f16,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f67,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f16])).
% 2.78/1.00  
% 2.78/1.00  fof(f74,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f66,f67])).
% 2.78/1.00  
% 2.78/1.00  fof(f75,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f65,f74])).
% 2.78/1.00  
% 2.78/1.00  fof(f76,plain,(
% 2.78/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f64,f75])).
% 2.78/1.00  
% 2.78/1.00  fof(f86,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f69,f76])).
% 2.78/1.00  
% 2.78/1.00  fof(f8,axiom,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f24,plain,(
% 2.78/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.78/1.00    inference(ennf_transformation,[],[f8])).
% 2.78/1.00  
% 2.78/1.00  fof(f59,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f24])).
% 2.78/1.00  
% 2.78/1.00  fof(f18,axiom,(
% 2.78/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f70,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f11,axiom,(
% 2.78/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f62,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f11])).
% 2.78/1.00  
% 2.78/1.00  fof(f6,axiom,(
% 2.78/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f57,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f6])).
% 2.78/1.00  
% 2.78/1.00  fof(f73,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f62,f57])).
% 2.78/1.00  
% 2.78/1.00  fof(f88,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.78/1.00    inference(definition_unfolding,[],[f70,f73,f75])).
% 2.78/1.00  
% 2.78/1.00  fof(f2,axiom,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f22,plain,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f2])).
% 2.78/1.00  
% 2.78/1.00  fof(f26,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(nnf_transformation,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f27,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(rectify,[],[f26])).
% 2.78/1.00  
% 2.78/1.00  fof(f28,plain,(
% 2.78/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f29,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.78/1.00  
% 2.78/1.00  fof(f43,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f29])).
% 2.78/1.00  
% 2.78/1.00  fof(f12,axiom,(
% 2.78/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f63,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f12])).
% 2.78/1.00  
% 2.78/1.00  fof(f85,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f63,f75,f75])).
% 2.78/1.00  
% 2.78/1.00  fof(f7,axiom,(
% 2.78/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f58,plain,(
% 2.78/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f7])).
% 2.78/1.00  
% 2.78/1.00  fof(f83,plain,(
% 2.78/1.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.78/1.00    inference(definition_unfolding,[],[f58,f73])).
% 2.78/1.00  
% 2.78/1.00  fof(f9,axiom,(
% 2.78/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f60,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f9])).
% 2.78/1.00  
% 2.78/1.00  fof(f84,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 2.78/1.00    inference(definition_unfolding,[],[f60,f73,f73,f57])).
% 2.78/1.00  
% 2.78/1.00  fof(f3,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f30,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(nnf_transformation,[],[f3])).
% 2.78/1.00  
% 2.78/1.00  fof(f31,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(flattening,[],[f30])).
% 2.78/1.00  
% 2.78/1.00  fof(f32,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(rectify,[],[f31])).
% 2.78/1.00  
% 2.78/1.00  fof(f33,plain,(
% 2.78/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f34,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 2.78/1.00  
% 2.78/1.00  fof(f46,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f81,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.78/1.00    inference(definition_unfolding,[],[f46,f57])).
% 2.78/1.00  
% 2.78/1.00  fof(f91,plain,(
% 2.78/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.78/1.00    inference(equality_resolution,[],[f81])).
% 2.78/1.00  
% 2.78/1.00  fof(f5,axiom,(
% 2.78/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f37,plain,(
% 2.78/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/1.00    inference(nnf_transformation,[],[f5])).
% 2.78/1.00  
% 2.78/1.00  fof(f38,plain,(
% 2.78/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/1.00    inference(flattening,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f54,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.78/1.00    inference(cnf_transformation,[],[f38])).
% 2.78/1.00  
% 2.78/1.00  fof(f94,plain,(
% 2.78/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.78/1.00    inference(equality_resolution,[],[f54])).
% 2.78/1.00  
% 2.78/1.00  fof(f45,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f82,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.78/1.00    inference(definition_unfolding,[],[f45,f57])).
% 2.78/1.00  
% 2.78/1.00  fof(f92,plain,(
% 2.78/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.78/1.00    inference(equality_resolution,[],[f82])).
% 2.78/1.00  
% 2.78/1.00  fof(f56,plain,(
% 2.78/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f38])).
% 2.78/1.00  
% 2.78/1.00  fof(f72,plain,(
% 2.78/1.00    k2_xboole_0(k1_tarski(sK3),sK4) != sK4),
% 2.78/1.00    inference(cnf_transformation,[],[f41])).
% 2.78/1.00  
% 2.78/1.00  fof(f89,plain,(
% 2.78/1.00    k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) != sK4),
% 2.78/1.00    inference(definition_unfolding,[],[f72,f73,f76])).
% 2.78/1.00  
% 2.78/1.00  cnf(c_24,negated_conjecture,
% 2.78/1.00      ( r2_hidden(sK3,sK4) ),
% 2.78/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_995,plain,
% 2.78/1.00      ( r2_hidden(sK3,sK4) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_20,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_997,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.78/1.00      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_16,plain,
% 2.78/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_999,plain,
% 2.78/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2202,plain,
% 2.78/1.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 2.78/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_997,c_999]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5378,plain,
% 2.78/1.00      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_995,c_2202]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_22,plain,
% 2.78/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5428,plain,
% 2.78/1.00      ( k5_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_5378,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1,plain,
% 2.78/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1012,plain,
% 2.78/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_19,plain,
% 2.78/1.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1346,plain,
% 2.78/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_19,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_15,plain,
% 2.78/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1350,plain,
% 2.78/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_22,c_15]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1918,plain,
% 2.78/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1346,c_1350]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_17,plain,
% 2.78/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2026,plain,
% 2.78/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1918,c_17]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2028,plain,
% 2.78/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_2026,c_1918]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2030,plain,
% 2.78/1.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_2028,c_1918]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2166,plain,
% 2.78/1.00      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_2030,c_15]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_7,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1006,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.78/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3356,plain,
% 2.78/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_2166,c_1006]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4053,plain,
% 2.78/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1012,c_3356]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4086,plain,
% 2.78/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_4053,c_999]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4197,plain,
% 2.78/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_4086,c_2166]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_14,plain,
% 2.78/1.00      ( r1_tarski(X0,X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1000,plain,
% 2.78/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1220,plain,
% 2.78/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1000,c_999]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3357,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.78/1.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1220,c_1006]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_8,plain,
% 2.78/1.00      ( r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1005,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.78/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3093,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.78/1.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1220,c_1005]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4744,plain,
% 2.78/1.00      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_3357,c_3093]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4751,plain,
% 2.78/1.00      ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1012,c_4744]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_12,plain,
% 2.78/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1001,plain,
% 2.78/1.00      ( X0 = X1
% 2.78/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.78/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4085,plain,
% 2.78/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_4053,c_1001]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4789,plain,
% 2.78/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_4751,c_4085]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5430,plain,
% 2.78/1.00      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_5428,c_4197,c_4789]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_23,negated_conjecture,
% 2.78/1.00      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) != sK4 ),
% 2.78/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1908,plain,
% 2.78/1.00      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_1346,c_23]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(contradiction,plain,
% 2.78/1.01      ( $false ),
% 2.78/1.01      inference(minisat,[status(thm)],[c_5430,c_1908]) ).
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  ------                               Statistics
% 2.78/1.01  
% 2.78/1.01  ------ General
% 2.78/1.01  
% 2.78/1.01  abstr_ref_over_cycles:                  0
% 2.78/1.01  abstr_ref_under_cycles:                 0
% 2.78/1.01  gc_basic_clause_elim:                   0
% 2.78/1.01  forced_gc_time:                         0
% 2.78/1.01  parsing_time:                           0.009
% 2.78/1.01  unif_index_cands_time:                  0.
% 2.78/1.01  unif_index_add_time:                    0.
% 2.78/1.01  orderings_time:                         0.
% 2.78/1.01  out_proof_time:                         0.008
% 2.78/1.01  total_time:                             0.183
% 2.78/1.01  num_of_symbols:                         44
% 2.78/1.01  num_of_terms:                           6431
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing
% 2.78/1.01  
% 2.78/1.01  num_of_splits:                          0
% 2.78/1.01  num_of_split_atoms:                     0
% 2.78/1.01  num_of_reused_defs:                     0
% 2.78/1.01  num_eq_ax_congr_red:                    27
% 2.78/1.01  num_of_sem_filtered_clauses:            1
% 2.78/1.01  num_of_subtypes:                        0
% 2.78/1.01  monotx_restored_types:                  0
% 2.78/1.01  sat_num_of_epr_types:                   0
% 2.78/1.01  sat_num_of_non_cyclic_types:            0
% 2.78/1.01  sat_guarded_non_collapsed_types:        0
% 2.78/1.01  num_pure_diseq_elim:                    0
% 2.78/1.01  simp_replaced_by:                       0
% 2.78/1.01  res_preprocessed:                       115
% 2.78/1.01  prep_upred:                             0
% 2.78/1.01  prep_unflattend:                        4
% 2.78/1.01  smt_new_axioms:                         0
% 2.78/1.01  pred_elim_cands:                        3
% 2.78/1.01  pred_elim:                              0
% 2.78/1.01  pred_elim_cl:                           0
% 2.78/1.01  pred_elim_cycles:                       2
% 2.78/1.01  merged_defs:                            8
% 2.78/1.01  merged_defs_ncl:                        0
% 2.78/1.01  bin_hyper_res:                          8
% 2.78/1.01  prep_cycles:                            4
% 2.78/1.01  pred_elim_time:                         0.002
% 2.78/1.01  splitting_time:                         0.
% 2.78/1.01  sem_filter_time:                        0.
% 2.78/1.01  monotx_time:                            0.001
% 2.78/1.01  subtype_inf_time:                       0.
% 2.78/1.01  
% 2.78/1.01  ------ Problem properties
% 2.78/1.01  
% 2.78/1.01  clauses:                                24
% 2.78/1.01  conjectures:                            2
% 2.78/1.01  epr:                                    6
% 2.78/1.01  horn:                                   17
% 2.78/1.01  ground:                                 2
% 2.78/1.01  unary:                                  8
% 2.78/1.01  binary:                                 9
% 2.78/1.01  lits:                                   48
% 2.78/1.01  lits_eq:                                10
% 2.78/1.01  fd_pure:                                0
% 2.78/1.01  fd_pseudo:                              0
% 2.78/1.01  fd_cond:                                0
% 2.78/1.01  fd_pseudo_cond:                         4
% 2.78/1.01  ac_symbols:                             0
% 2.78/1.01  
% 2.78/1.01  ------ Propositional Solver
% 2.78/1.01  
% 2.78/1.01  prop_solver_calls:                      27
% 2.78/1.01  prop_fast_solver_calls:                 610
% 2.78/1.01  smt_solver_calls:                       0
% 2.78/1.01  smt_fast_solver_calls:                  0
% 2.78/1.01  prop_num_of_clauses:                    2077
% 2.78/1.01  prop_preprocess_simplified:             6107
% 2.78/1.01  prop_fo_subsumed:                       2
% 2.78/1.01  prop_solver_time:                       0.
% 2.78/1.01  smt_solver_time:                        0.
% 2.78/1.01  smt_fast_solver_time:                   0.
% 2.78/1.01  prop_fast_solver_time:                  0.
% 2.78/1.01  prop_unsat_core_time:                   0.
% 2.78/1.01  
% 2.78/1.01  ------ QBF
% 2.78/1.01  
% 2.78/1.01  qbf_q_res:                              0
% 2.78/1.01  qbf_num_tautologies:                    0
% 2.78/1.01  qbf_prep_cycles:                        0
% 2.78/1.01  
% 2.78/1.01  ------ BMC1
% 2.78/1.01  
% 2.78/1.01  bmc1_current_bound:                     -1
% 2.78/1.01  bmc1_last_solved_bound:                 -1
% 2.78/1.01  bmc1_unsat_core_size:                   -1
% 2.78/1.01  bmc1_unsat_core_parents_size:           -1
% 2.78/1.01  bmc1_merge_next_fun:                    0
% 2.78/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation
% 2.78/1.01  
% 2.78/1.01  inst_num_of_clauses:                    570
% 2.78/1.01  inst_num_in_passive:                    67
% 2.78/1.01  inst_num_in_active:                     238
% 2.78/1.01  inst_num_in_unprocessed:                265
% 2.78/1.01  inst_num_of_loops:                      270
% 2.78/1.01  inst_num_of_learning_restarts:          0
% 2.78/1.01  inst_num_moves_active_passive:          30
% 2.78/1.01  inst_lit_activity:                      0
% 2.78/1.01  inst_lit_activity_moves:                0
% 2.78/1.01  inst_num_tautologies:                   0
% 2.78/1.01  inst_num_prop_implied:                  0
% 2.78/1.01  inst_num_existing_simplified:           0
% 2.78/1.01  inst_num_eq_res_simplified:             0
% 2.78/1.01  inst_num_child_elim:                    0
% 2.78/1.01  inst_num_of_dismatching_blockings:      345
% 2.78/1.01  inst_num_of_non_proper_insts:           581
% 2.78/1.01  inst_num_of_duplicates:                 0
% 2.78/1.01  inst_inst_num_from_inst_to_res:         0
% 2.78/1.01  inst_dismatching_checking_time:         0.
% 2.78/1.01  
% 2.78/1.01  ------ Resolution
% 2.78/1.01  
% 2.78/1.01  res_num_of_clauses:                     0
% 2.78/1.01  res_num_in_passive:                     0
% 2.78/1.01  res_num_in_active:                      0
% 2.78/1.01  res_num_of_loops:                       119
% 2.78/1.01  res_forward_subset_subsumed:            41
% 2.78/1.01  res_backward_subset_subsumed:           0
% 2.78/1.01  res_forward_subsumed:                   0
% 2.78/1.01  res_backward_subsumed:                  0
% 2.78/1.01  res_forward_subsumption_resolution:     0
% 2.78/1.01  res_backward_subsumption_resolution:    0
% 2.78/1.01  res_clause_to_clause_subsumption:       369
% 2.78/1.01  res_orphan_elimination:                 0
% 2.78/1.01  res_tautology_del:                      58
% 2.78/1.01  res_num_eq_res_simplified:              0
% 2.78/1.01  res_num_sel_changes:                    0
% 2.78/1.01  res_moves_from_active_to_pass:          0
% 2.78/1.01  
% 2.78/1.01  ------ Superposition
% 2.78/1.01  
% 2.78/1.01  sup_time_total:                         0.
% 2.78/1.01  sup_time_generating:                    0.
% 2.78/1.01  sup_time_sim_full:                      0.
% 2.78/1.01  sup_time_sim_immed:                     0.
% 2.78/1.01  
% 2.78/1.01  sup_num_of_clauses:                     91
% 2.78/1.01  sup_num_in_active:                      44
% 2.78/1.01  sup_num_in_passive:                     47
% 2.78/1.01  sup_num_of_loops:                       53
% 2.78/1.01  sup_fw_superposition:                   129
% 2.78/1.01  sup_bw_superposition:                   89
% 2.78/1.01  sup_immediate_simplified:               50
% 2.78/1.01  sup_given_eliminated:                   2
% 2.78/1.01  comparisons_done:                       0
% 2.78/1.01  comparisons_avoided:                    0
% 2.78/1.01  
% 2.78/1.01  ------ Simplifications
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  sim_fw_subset_subsumed:                 6
% 2.78/1.01  sim_bw_subset_subsumed:                 4
% 2.78/1.01  sim_fw_subsumed:                        7
% 2.78/1.01  sim_bw_subsumed:                        0
% 2.78/1.01  sim_fw_subsumption_res:                 0
% 2.78/1.01  sim_bw_subsumption_res:                 0
% 2.78/1.01  sim_tautology_del:                      14
% 2.78/1.01  sim_eq_tautology_del:                   19
% 2.78/1.01  sim_eq_res_simp:                        1
% 2.78/1.01  sim_fw_demodulated:                     24
% 2.78/1.01  sim_bw_demodulated:                     10
% 2.78/1.01  sim_light_normalised:                   32
% 2.78/1.01  sim_joinable_taut:                      0
% 2.78/1.01  sim_joinable_simp:                      0
% 2.78/1.01  sim_ac_normalised:                      0
% 2.78/1.01  sim_smt_subsumption:                    0
% 2.78/1.01  
%------------------------------------------------------------------------------
