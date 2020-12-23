%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:10 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 195 expanded)
%              Number of clauses        :   36 (  41 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  306 ( 477 expanded)
%              Number of equality atoms :  137 ( 262 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f86,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK4 = sK5
        | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4) )
      & ( sK4 != sK5
        | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( sK4 = sK5
      | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4) )
    & ( sK4 != sK5
      | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).

fof(f69,plain,
    ( sK4 = sK5
    | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,
    ( sK4 = sK5
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f69,f56,f71,f71,f71])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f68,plain,
    ( sK4 != sK5
    | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,
    ( sK4 != sK5
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f68,f56,f71,f71,f71])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f84,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f75])).

fof(f85,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f84])).

cnf(c_20,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_760,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_766,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_768,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1359,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_768])).

cnf(c_1573,plain,
    ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_1359])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_761,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6586,plain,
    ( X0 = X1
    | k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1573,c_761])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 = sK5 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11903,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_6586,c_22])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_765,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1572,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_765,c_1359])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1589,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1572,c_14])).

cnf(c_11922,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_11903,c_1589])).

cnf(c_11923,plain,
    ( sK5 = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_11922])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_12851,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_11923,c_23])).

cnf(c_12853,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_12851])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_770,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12861,plain,
    ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12853,c_770])).

cnf(c_12884,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12861])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_942,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X0,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1425,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X0,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1428,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top
    | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_1430,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_35,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12884,c_1430,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:53 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.70/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.00  
% 3.70/1.00  ------  iProver source info
% 3.70/1.00  
% 3.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.00  git: non_committed_changes: false
% 3.70/1.00  git: last_make_outside_of_git: false
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    --mode clausify
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         false
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     num_symb
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       true
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     false
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   []
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_full_bw                           [BwDemod]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  ------ Parsing...
% 3.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.00  ------ Proving...
% 3.70/1.00  ------ Problem Properties 
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  clauses                                 24
% 3.70/1.00  conjectures                             2
% 3.70/1.00  EPR                                     2
% 3.70/1.00  Horn                                    15
% 3.70/1.00  unary                                   4
% 3.70/1.00  binary                                  10
% 3.70/1.00  lits                                    55
% 3.70/1.00  lits eq                                 14
% 3.70/1.00  fd_pure                                 0
% 3.70/1.00  fd_pseudo                               0
% 3.70/1.00  fd_cond                                 1
% 3.70/1.00  fd_pseudo_cond                          5
% 3.70/1.00  AC symbols                              0
% 3.70/1.00  
% 3.70/1.00  ------ Schedule dynamic 5 is on 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  Current options:
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    --mode clausify
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         false
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     none
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       false
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     false
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   []
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_full_bw                           [BwDemod]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ Proving...
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS status Theorem for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  fof(f13,axiom,(
% 3.70/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f22,plain,(
% 3.70/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f13])).
% 3.70/1.00  
% 3.70/1.00  fof(f66,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f22])).
% 3.70/1.00  
% 3.70/1.00  fof(f10,axiom,(
% 3.70/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f63,plain,(
% 3.70/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f10])).
% 3.70/1.00  
% 3.70/1.00  fof(f11,axiom,(
% 3.70/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f64,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f11])).
% 3.70/1.00  
% 3.70/1.00  fof(f12,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f65,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f12])).
% 3.70/1.00  
% 3.70/1.00  fof(f70,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f64,f65])).
% 3.70/1.00  
% 3.70/1.00  fof(f71,plain,(
% 3.70/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f63,f70])).
% 3.70/1.00  
% 3.70/1.00  fof(f77,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f66,f71])).
% 3.70/1.00  
% 3.70/1.00  fof(f5,axiom,(
% 3.70/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f21,plain,(
% 3.70/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.70/1.00    inference(ennf_transformation,[],[f5])).
% 3.70/1.00  
% 3.70/1.00  fof(f33,plain,(
% 3.70/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f34,plain,(
% 3.70/1.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).
% 3.70/1.00  
% 3.70/1.00  fof(f55,plain,(
% 3.70/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f34])).
% 3.70/1.00  
% 3.70/1.00  fof(f4,axiom,(
% 3.70/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f17,plain,(
% 3.70/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.70/1.00    inference(rectify,[],[f4])).
% 3.70/1.00  
% 3.70/1.00  fof(f20,plain,(
% 3.70/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.70/1.00    inference(ennf_transformation,[],[f17])).
% 3.70/1.00  
% 3.70/1.00  fof(f31,plain,(
% 3.70/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f32,plain,(
% 3.70/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f31])).
% 3.70/1.00  
% 3.70/1.00  fof(f54,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f32])).
% 3.70/1.00  
% 3.70/1.00  fof(f9,axiom,(
% 3.70/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f35,plain,(
% 3.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.70/1.00    inference(nnf_transformation,[],[f9])).
% 3.70/1.00  
% 3.70/1.00  fof(f36,plain,(
% 3.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.70/1.00    inference(rectify,[],[f35])).
% 3.70/1.00  
% 3.70/1.00  fof(f37,plain,(
% 3.70/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f38,plain,(
% 3.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 3.70/1.00  
% 3.70/1.00  fof(f59,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.70/1.00    inference(cnf_transformation,[],[f38])).
% 3.70/1.00  
% 3.70/1.00  fof(f76,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.70/1.00    inference(definition_unfolding,[],[f59,f71])).
% 3.70/1.00  
% 3.70/1.00  fof(f86,plain,(
% 3.70/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.70/1.00    inference(equality_resolution,[],[f76])).
% 3.70/1.00  
% 3.70/1.00  fof(f15,conjecture,(
% 3.70/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f16,negated_conjecture,(
% 3.70/1.00    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.70/1.00    inference(negated_conjecture,[],[f15])).
% 3.70/1.00  
% 3.70/1.00  fof(f24,plain,(
% 3.70/1.00    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 3.70/1.00    inference(ennf_transformation,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f39,plain,(
% 3.70/1.00    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 3.70/1.00    inference(nnf_transformation,[],[f24])).
% 3.70/1.00  
% 3.70/1.00  fof(f40,plain,(
% 3.70/1.00    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK4 = sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4)) & (sK4 != sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f41,plain,(
% 3.70/1.00    (sK4 = sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4)) & (sK4 != sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).
% 3.70/1.00  
% 3.70/1.00  fof(f69,plain,(
% 3.70/1.00    sK4 = sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4)),
% 3.70/1.00    inference(cnf_transformation,[],[f41])).
% 3.70/1.00  
% 3.70/1.00  fof(f6,axiom,(
% 3.70/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f56,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f6])).
% 3.70/1.00  
% 3.70/1.00  fof(f79,plain,(
% 3.70/1.00    sK4 = sK5 | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4)),
% 3.70/1.00    inference(definition_unfolding,[],[f69,f56,f71,f71,f71])).
% 3.70/1.00  
% 3.70/1.00  fof(f8,axiom,(
% 3.70/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f58,plain,(
% 3.70/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f8])).
% 3.70/1.00  
% 3.70/1.00  fof(f7,axiom,(
% 3.70/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f57,plain,(
% 3.70/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f7])).
% 3.70/1.00  
% 3.70/1.00  fof(f72,plain,(
% 3.70/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.70/1.00    inference(definition_unfolding,[],[f57,f56])).
% 3.70/1.00  
% 3.70/1.00  fof(f68,plain,(
% 3.70/1.00    sK4 != sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.70/1.00    inference(cnf_transformation,[],[f41])).
% 3.70/1.00  
% 3.70/1.00  fof(f80,plain,(
% 3.70/1.00    sK4 != sK5 | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)),
% 3.70/1.00    inference(definition_unfolding,[],[f68,f56,f71,f71,f71])).
% 3.70/1.00  
% 3.70/1.00  fof(f3,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f19,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.70/1.00    inference(ennf_transformation,[],[f3])).
% 3.70/1.00  
% 3.70/1.00  fof(f30,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.70/1.00    inference(nnf_transformation,[],[f19])).
% 3.70/1.00  
% 3.70/1.00  fof(f50,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  fof(f1,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f25,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.70/1.00    inference(nnf_transformation,[],[f1])).
% 3.70/1.00  
% 3.70/1.00  fof(f26,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.70/1.00    inference(flattening,[],[f25])).
% 3.70/1.00  
% 3.70/1.00  fof(f27,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.70/1.00    inference(rectify,[],[f26])).
% 3.70/1.00  
% 3.70/1.00  fof(f28,plain,(
% 3.70/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f29,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.70/1.00  
% 3.70/1.00  fof(f44,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.70/1.00    inference(cnf_transformation,[],[f29])).
% 3.70/1.00  
% 3.70/1.00  fof(f81,plain,(
% 3.70/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.70/1.00    inference(equality_resolution,[],[f44])).
% 3.70/1.00  
% 3.70/1.00  fof(f60,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.70/1.00    inference(cnf_transformation,[],[f38])).
% 3.70/1.00  
% 3.70/1.00  fof(f75,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.70/1.00    inference(definition_unfolding,[],[f60,f71])).
% 3.70/1.00  
% 3.70/1.00  fof(f84,plain,(
% 3.70/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.70/1.00    inference(equality_resolution,[],[f75])).
% 3.70/1.00  
% 3.70/1.00  fof(f85,plain,(
% 3.70/1.00    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.70/1.00    inference(equality_resolution,[],[f84])).
% 3.70/1.00  
% 3.70/1.00  cnf(c_20,plain,
% 3.70/1.00      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_760,plain,
% 3.70/1.00      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 3.70/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13,plain,
% 3.70/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_766,plain,
% 3.70/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11,plain,
% 3.70/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_768,plain,
% 3.70/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.70/1.00      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1359,plain,
% 3.70/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.70/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_766,c_768]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1573,plain,
% 3.70/1.00      ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
% 3.70/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_760,c_1359]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_19,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.70/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_761,plain,
% 3.70/1.00      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6586,plain,
% 3.70/1.00      ( X0 = X1
% 3.70/1.00      | k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1573,c_761]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_22,negated_conjecture,
% 3.70/1.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4)
% 3.70/1.00      | sK4 = sK5 ),
% 3.70/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11903,plain,
% 3.70/1.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) != k2_enumset1(sK4,sK4,sK4,sK4)
% 3.70/1.00      | sK5 = sK4 ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_6586,c_22]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_15,plain,
% 3.70/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_765,plain,
% 3.70/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1572,plain,
% 3.70/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_765,c_1359]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14,plain,
% 3.70/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1589,plain,
% 3.70/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_1572,c_14]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11922,plain,
% 3.70/1.00      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 3.70/1.00      | sK5 = sK4 ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_11903,c_1589]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11923,plain,
% 3.70/1.00      ( sK5 = sK4 ),
% 3.70/1.00      inference(equality_resolution_simp,[status(thm)],[c_11922]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_23,negated_conjecture,
% 3.70/1.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
% 3.70/1.00      | sK4 != sK5 ),
% 3.70/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12851,plain,
% 3.70/1.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4)
% 3.70/1.00      | sK4 != sK4 ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_11923,c_23]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12853,plain,
% 3.70/1.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.70/1.00      inference(equality_resolution_simp,[status(thm)],[c_12851]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,X1)
% 3.70/1.00      | ~ r2_hidden(X0,X2)
% 3.70/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_770,plain,
% 3.70/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.70/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.70/1.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12861,plain,
% 3.70/1.00      ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 3.70/1.00      | r2_hidden(X0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12853,c_770]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12884,plain,
% 3.70/1.00      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 3.70/1.00      | r2_hidden(sK4,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_12861]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,X1)
% 3.70/1.00      | ~ r2_hidden(X0,X2)
% 3.70/1.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_942,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,X1)
% 3.70/1.00      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 3.70/1.00      | r2_hidden(X0,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1425,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
% 3.70/1.00      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 3.70/1.00      | r2_hidden(X0,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_942]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1428,plain,
% 3.70/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top
% 3.70/1.00      | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 3.70/1.00      | r2_hidden(X0,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1430,plain,
% 3.70/1.00      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 3.70/1.00      | r2_hidden(sK4,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1428]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_18,plain,
% 3.70/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_33,plain,
% 3.70/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_35,plain,
% 3.70/1.00      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(contradiction,plain,
% 3.70/1.00      ( $false ),
% 3.70/1.00      inference(minisat,[status(thm)],[c_12884,c_1430,c_35]) ).
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  ------                               Statistics
% 3.70/1.00  
% 3.70/1.00  ------ General
% 3.70/1.00  
% 3.70/1.00  abstr_ref_over_cycles:                  0
% 3.70/1.00  abstr_ref_under_cycles:                 0
% 3.70/1.00  gc_basic_clause_elim:                   0
% 3.70/1.00  forced_gc_time:                         0
% 3.70/1.00  parsing_time:                           0.009
% 3.70/1.00  unif_index_cands_time:                  0.
% 3.70/1.00  unif_index_add_time:                    0.
% 3.70/1.00  orderings_time:                         0.
% 3.70/1.00  out_proof_time:                         0.032
% 3.70/1.00  total_time:                             0.402
% 3.70/1.00  num_of_symbols:                         43
% 3.70/1.00  num_of_terms:                           15797
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing
% 3.70/1.00  
% 3.70/1.00  num_of_splits:                          0
% 3.70/1.00  num_of_split_atoms:                     0
% 3.70/1.00  num_of_reused_defs:                     0
% 3.70/1.00  num_eq_ax_congr_red:                    16
% 3.70/1.00  num_of_sem_filtered_clauses:            1
% 3.70/1.00  num_of_subtypes:                        0
% 3.70/1.00  monotx_restored_types:                  0
% 3.70/1.00  sat_num_of_epr_types:                   0
% 3.70/1.00  sat_num_of_non_cyclic_types:            0
% 3.70/1.00  sat_guarded_non_collapsed_types:        0
% 3.70/1.00  num_pure_diseq_elim:                    0
% 3.70/1.00  simp_replaced_by:                       0
% 3.70/1.00  res_preprocessed:                       87
% 3.70/1.00  prep_upred:                             0
% 3.70/1.00  prep_unflattend:                        0
% 3.70/1.00  smt_new_axioms:                         0
% 3.70/1.00  pred_elim_cands:                        2
% 3.70/1.00  pred_elim:                              0
% 3.70/1.00  pred_elim_cl:                           0
% 3.70/1.00  pred_elim_cycles:                       1
% 3.70/1.00  merged_defs:                            6
% 3.70/1.00  merged_defs_ncl:                        0
% 3.70/1.00  bin_hyper_res:                          6
% 3.70/1.00  prep_cycles:                            3
% 3.70/1.00  pred_elim_time:                         0.
% 3.70/1.00  splitting_time:                         0.
% 3.70/1.00  sem_filter_time:                        0.
% 3.70/1.00  monotx_time:                            0.
% 3.70/1.00  subtype_inf_time:                       0.
% 3.70/1.00  
% 3.70/1.00  ------ Problem properties
% 3.70/1.00  
% 3.70/1.00  clauses:                                24
% 3.70/1.00  conjectures:                            2
% 3.70/1.00  epr:                                    2
% 3.70/1.00  horn:                                   15
% 3.70/1.00  ground:                                 2
% 3.70/1.00  unary:                                  4
% 3.70/1.00  binary:                                 10
% 3.70/1.00  lits:                                   55
% 3.70/1.00  lits_eq:                                14
% 3.70/1.00  fd_pure:                                0
% 3.70/1.00  fd_pseudo:                              0
% 3.70/1.00  fd_cond:                                1
% 3.70/1.00  fd_pseudo_cond:                         5
% 3.70/1.00  ac_symbols:                             0
% 3.70/1.00  
% 3.70/1.00  ------ Propositional Solver
% 3.70/1.00  
% 3.70/1.00  prop_solver_calls:                      23
% 3.70/1.00  prop_fast_solver_calls:                 658
% 3.70/1.00  smt_solver_calls:                       0
% 3.70/1.00  smt_fast_solver_calls:                  0
% 3.70/1.00  prop_num_of_clauses:                    5051
% 3.70/1.00  prop_preprocess_simplified:             8953
% 3.70/1.00  prop_fo_subsumed:                       5
% 3.70/1.00  prop_solver_time:                       0.
% 3.70/1.00  smt_solver_time:                        0.
% 3.70/1.00  smt_fast_solver_time:                   0.
% 3.70/1.00  prop_fast_solver_time:                  0.
% 3.70/1.00  prop_unsat_core_time:                   0.001
% 3.70/1.00  
% 3.70/1.00  ------ QBF
% 3.70/1.00  
% 3.70/1.00  qbf_q_res:                              0
% 3.70/1.00  qbf_num_tautologies:                    0
% 3.70/1.00  qbf_prep_cycles:                        0
% 3.70/1.00  
% 3.70/1.00  ------ BMC1
% 3.70/1.00  
% 3.70/1.00  bmc1_current_bound:                     -1
% 3.70/1.00  bmc1_last_solved_bound:                 -1
% 3.70/1.00  bmc1_unsat_core_size:                   -1
% 3.70/1.00  bmc1_unsat_core_parents_size:           -1
% 3.70/1.00  bmc1_merge_next_fun:                    0
% 3.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation
% 3.70/1.00  
% 3.70/1.00  inst_num_of_clauses:                    1121
% 3.70/1.00  inst_num_in_passive:                    189
% 3.70/1.00  inst_num_in_active:                     395
% 3.70/1.00  inst_num_in_unprocessed:                537
% 3.70/1.00  inst_num_of_loops:                      500
% 3.70/1.00  inst_num_of_learning_restarts:          0
% 3.70/1.00  inst_num_moves_active_passive:          104
% 3.70/1.00  inst_lit_activity:                      0
% 3.70/1.00  inst_lit_activity_moves:                0
% 3.70/1.00  inst_num_tautologies:                   0
% 3.70/1.00  inst_num_prop_implied:                  0
% 3.70/1.00  inst_num_existing_simplified:           0
% 3.70/1.00  inst_num_eq_res_simplified:             0
% 3.70/1.00  inst_num_child_elim:                    0
% 3.70/1.00  inst_num_of_dismatching_blockings:      540
% 3.70/1.00  inst_num_of_non_proper_insts:           911
% 3.70/1.00  inst_num_of_duplicates:                 0
% 3.70/1.00  inst_inst_num_from_inst_to_res:         0
% 3.70/1.00  inst_dismatching_checking_time:         0.
% 3.70/1.00  
% 3.70/1.00  ------ Resolution
% 3.70/1.00  
% 3.70/1.00  res_num_of_clauses:                     0
% 3.70/1.00  res_num_in_passive:                     0
% 3.70/1.00  res_num_in_active:                      0
% 3.70/1.00  res_num_of_loops:                       90
% 3.70/1.00  res_forward_subset_subsumed:            129
% 3.70/1.00  res_backward_subset_subsumed:           2
% 3.70/1.00  res_forward_subsumed:                   0
% 3.70/1.00  res_backward_subsumed:                  0
% 3.70/1.00  res_forward_subsumption_resolution:     0
% 3.70/1.00  res_backward_subsumption_resolution:    0
% 3.70/1.00  res_clause_to_clause_subsumption:       4614
% 3.70/1.00  res_orphan_elimination:                 0
% 3.70/1.00  res_tautology_del:                      38
% 3.70/1.00  res_num_eq_res_simplified:              0
% 3.70/1.00  res_num_sel_changes:                    0
% 3.70/1.00  res_moves_from_active_to_pass:          0
% 3.70/1.00  
% 3.70/1.00  ------ Superposition
% 3.70/1.00  
% 3.70/1.00  sup_time_total:                         0.
% 3.70/1.00  sup_time_generating:                    0.
% 3.70/1.00  sup_time_sim_full:                      0.
% 3.70/1.00  sup_time_sim_immed:                     0.
% 3.70/1.00  
% 3.70/1.00  sup_num_of_clauses:                     464
% 3.70/1.00  sup_num_in_active:                      97
% 3.70/1.00  sup_num_in_passive:                     367
% 3.70/1.00  sup_num_of_loops:                       99
% 3.70/1.00  sup_fw_superposition:                   378
% 3.70/1.00  sup_bw_superposition:                   373
% 3.70/1.00  sup_immediate_simplified:               198
% 3.70/1.00  sup_given_eliminated:                   0
% 3.70/1.00  comparisons_done:                       0
% 3.70/1.00  comparisons_avoided:                    15
% 3.70/1.00  
% 3.70/1.00  ------ Simplifications
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  sim_fw_subset_subsumed:                 23
% 3.70/1.00  sim_bw_subset_subsumed:                 7
% 3.70/1.00  sim_fw_subsumed:                        50
% 3.70/1.00  sim_bw_subsumed:                        1
% 3.70/1.00  sim_fw_subsumption_res:                 3
% 3.70/1.00  sim_bw_subsumption_res:                 0
% 3.70/1.00  sim_tautology_del:                      21
% 3.70/1.00  sim_eq_tautology_del:                   21
% 3.70/1.00  sim_eq_res_simp:                        5
% 3.70/1.00  sim_fw_demodulated:                     119
% 3.70/1.00  sim_bw_demodulated:                     3
% 3.70/1.00  sim_light_normalised:                   40
% 3.70/1.00  sim_joinable_taut:                      0
% 3.70/1.00  sim_joinable_simp:                      0
% 3.70/1.00  sim_ac_normalised:                      0
% 3.70/1.00  sim_smt_subsumption:                    0
% 3.70/1.00  
%------------------------------------------------------------------------------
