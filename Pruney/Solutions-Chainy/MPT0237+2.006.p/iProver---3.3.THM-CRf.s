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
% DateTime   : Thu Dec  3 11:31:42 EST 2020

% Result     : Theorem 35.69s
% Output     : CNFRefutation 35.69s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 574 expanded)
%              Number of clauses        :   80 ( 100 expanded)
%              Number of leaves         :   30 ( 167 expanded)
%              Depth                    :   20
%              Number of atoms          :  403 (1079 expanded)
%              Number of equality atoms :  238 ( 718 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f86])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f87])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f102,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f92])).

fof(f103,plain,(
    ! [X3] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f102])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f24,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f104,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f95,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f82,f86])).

fof(f22,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f22])).

fof(f31,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK4,sK5) != k3_tarski(k2_tarski(k1_tarski(sK4),k1_tarski(sK5))) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    k2_tarski(sK4,sK5) != k3_tarski(k2_tarski(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f47])).

fof(f81,plain,(
    k2_tarski(sK4,sK5) != k3_tarski(k2_tarski(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f81,f86,f86,f87,f87])).

fof(f21,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f80,f87])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f79,f87,f87,f86])).

cnf(c_19,plain,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1163,plain,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1179,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1174,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2248,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1174])).

cnf(c_17,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1165,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1168,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1173,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2005,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1174])).

cnf(c_2294,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_2005])).

cnf(c_2463,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_2294])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1177,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3898,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_1177])).

cnf(c_3955,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_3898])).

cnf(c_3961,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_3955])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1172,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4069,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3961,c_1172])).

cnf(c_4255,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_4069])).

cnf(c_4951,plain,
    ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_4255])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1164,plain,
    ( X0 = X1
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6290,plain,
    ( X0 = X1
    | k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4951,c_1164])).

cnf(c_20,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_24,negated_conjecture,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1564,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_20,c_24])).

cnf(c_1738,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_0,c_1564])).

cnf(c_50132,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0)) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_6290,c_1738])).

cnf(c_23,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1568,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_20,c_23])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1171,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1170,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1503,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1171,c_1170])).

cnf(c_1569,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1568,c_1503])).

cnf(c_50288,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
    | sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_50132,c_1569])).

cnf(c_726,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
    theory(equality)).

cnf(c_35049,plain,
    ( k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1439,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
    | sK5 != X6
    | sK4 != X0
    | sK4 != X1
    | sK4 != X2
    | sK4 != X3
    | sK4 != X4
    | sK4 != X5 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1908,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(X0,X1,X2,X3,X4,X5,sK5)
    | sK5 != sK5
    | sK4 != X0
    | sK4 != X1
    | sK4 != X2
    | sK4 != X3
    | sK4 != X4
    | sK4 != X5 ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_32070,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 != sK5
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_721,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_17842,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_17843,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_17842])).

cnf(c_727,plain,
    ( X0 != X1
    | k3_tarski(X0) = k3_tarski(X1) ),
    theory(equality)).

cnf(c_9525,plain,
    ( k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_1305,plain,
    ( X0 != X1
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != X1
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1730,plain,
    ( X0 != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = X0
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_4000,plain,
    ( k3_tarski(X0) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(X0)
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_8772,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_4000])).

cnf(c_6884,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1902,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5765,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_1207,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != X0
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1308,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(X0)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_3472,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)))
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_2258,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2027,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( X0 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1895,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k5_enumset1(X0,X0,X0,X0,X0,X0,sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1901,plain,
    ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_1300,plain,
    ( ~ r1_tarski(X0,k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),X0)
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1680,plain,
    ( ~ r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_1247,plain,
    ( X0 != X1
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != X1
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1459,plain,
    ( X0 != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = X0
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_1605,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)))
    | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1440,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK5 != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_720,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1278,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_38,plain,
    ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_35,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50288,c_35049,c_32070,c_17843,c_9525,c_8772,c_6884,c_5765,c_3472,c_2258,c_2027,c_1901,c_1680,c_1605,c_1440,c_1278,c_38,c_35,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.69/5.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.69/5.01  
% 35.69/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.69/5.01  
% 35.69/5.01  ------  iProver source info
% 35.69/5.01  
% 35.69/5.01  git: date: 2020-06-30 10:37:57 +0100
% 35.69/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.69/5.01  git: non_committed_changes: false
% 35.69/5.01  git: last_make_outside_of_git: false
% 35.69/5.01  
% 35.69/5.01  ------ 
% 35.69/5.01  
% 35.69/5.01  ------ Input Options
% 35.69/5.01  
% 35.69/5.01  --out_options                           all
% 35.69/5.01  --tptp_safe_out                         true
% 35.69/5.01  --problem_path                          ""
% 35.69/5.01  --include_path                          ""
% 35.69/5.01  --clausifier                            res/vclausify_rel
% 35.69/5.01  --clausifier_options                    ""
% 35.69/5.01  --stdin                                 false
% 35.69/5.01  --stats_out                             all
% 35.69/5.01  
% 35.69/5.01  ------ General Options
% 35.69/5.01  
% 35.69/5.01  --fof                                   false
% 35.69/5.01  --time_out_real                         305.
% 35.69/5.01  --time_out_virtual                      -1.
% 35.69/5.01  --symbol_type_check                     false
% 35.69/5.01  --clausify_out                          false
% 35.69/5.01  --sig_cnt_out                           false
% 35.69/5.01  --trig_cnt_out                          false
% 35.69/5.01  --trig_cnt_out_tolerance                1.
% 35.69/5.01  --trig_cnt_out_sk_spl                   false
% 35.69/5.01  --abstr_cl_out                          false
% 35.69/5.01  
% 35.69/5.01  ------ Global Options
% 35.69/5.01  
% 35.69/5.01  --schedule                              default
% 35.69/5.01  --add_important_lit                     false
% 35.69/5.01  --prop_solver_per_cl                    1000
% 35.69/5.01  --min_unsat_core                        false
% 35.69/5.01  --soft_assumptions                      false
% 35.69/5.01  --soft_lemma_size                       3
% 35.69/5.01  --prop_impl_unit_size                   0
% 35.69/5.01  --prop_impl_unit                        []
% 35.69/5.01  --share_sel_clauses                     true
% 35.69/5.01  --reset_solvers                         false
% 35.69/5.01  --bc_imp_inh                            [conj_cone]
% 35.69/5.01  --conj_cone_tolerance                   3.
% 35.69/5.01  --extra_neg_conj                        none
% 35.69/5.01  --large_theory_mode                     true
% 35.69/5.01  --prolific_symb_bound                   200
% 35.69/5.01  --lt_threshold                          2000
% 35.69/5.01  --clause_weak_htbl                      true
% 35.69/5.01  --gc_record_bc_elim                     false
% 35.69/5.01  
% 35.69/5.01  ------ Preprocessing Options
% 35.69/5.01  
% 35.69/5.01  --preprocessing_flag                    true
% 35.69/5.01  --time_out_prep_mult                    0.1
% 35.69/5.01  --splitting_mode                        input
% 35.69/5.01  --splitting_grd                         true
% 35.69/5.01  --splitting_cvd                         false
% 35.69/5.01  --splitting_cvd_svl                     false
% 35.69/5.01  --splitting_nvd                         32
% 35.69/5.01  --sub_typing                            true
% 35.69/5.01  --prep_gs_sim                           true
% 35.69/5.01  --prep_unflatten                        true
% 35.69/5.01  --prep_res_sim                          true
% 35.69/5.01  --prep_upred                            true
% 35.69/5.01  --prep_sem_filter                       exhaustive
% 35.69/5.01  --prep_sem_filter_out                   false
% 35.69/5.01  --pred_elim                             true
% 35.69/5.01  --res_sim_input                         true
% 35.69/5.01  --eq_ax_congr_red                       true
% 35.69/5.01  --pure_diseq_elim                       true
% 35.69/5.01  --brand_transform                       false
% 35.69/5.01  --non_eq_to_eq                          false
% 35.69/5.01  --prep_def_merge                        true
% 35.69/5.01  --prep_def_merge_prop_impl              false
% 35.69/5.01  --prep_def_merge_mbd                    true
% 35.69/5.01  --prep_def_merge_tr_red                 false
% 35.69/5.01  --prep_def_merge_tr_cl                  false
% 35.69/5.01  --smt_preprocessing                     true
% 35.69/5.01  --smt_ac_axioms                         fast
% 35.69/5.01  --preprocessed_out                      false
% 35.69/5.01  --preprocessed_stats                    false
% 35.69/5.01  
% 35.69/5.01  ------ Abstraction refinement Options
% 35.69/5.01  
% 35.69/5.01  --abstr_ref                             []
% 35.69/5.01  --abstr_ref_prep                        false
% 35.69/5.01  --abstr_ref_until_sat                   false
% 35.69/5.01  --abstr_ref_sig_restrict                funpre
% 35.69/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.69/5.01  --abstr_ref_under                       []
% 35.69/5.01  
% 35.69/5.01  ------ SAT Options
% 35.69/5.01  
% 35.69/5.01  --sat_mode                              false
% 35.69/5.01  --sat_fm_restart_options                ""
% 35.69/5.01  --sat_gr_def                            false
% 35.69/5.01  --sat_epr_types                         true
% 35.69/5.01  --sat_non_cyclic_types                  false
% 35.69/5.01  --sat_finite_models                     false
% 35.69/5.01  --sat_fm_lemmas                         false
% 35.69/5.01  --sat_fm_prep                           false
% 35.69/5.01  --sat_fm_uc_incr                        true
% 35.69/5.01  --sat_out_model                         small
% 35.69/5.01  --sat_out_clauses                       false
% 35.69/5.01  
% 35.69/5.01  ------ QBF Options
% 35.69/5.01  
% 35.69/5.01  --qbf_mode                              false
% 35.69/5.01  --qbf_elim_univ                         false
% 35.69/5.01  --qbf_dom_inst                          none
% 35.69/5.01  --qbf_dom_pre_inst                      false
% 35.69/5.01  --qbf_sk_in                             false
% 35.69/5.01  --qbf_pred_elim                         true
% 35.69/5.01  --qbf_split                             512
% 35.69/5.01  
% 35.69/5.01  ------ BMC1 Options
% 35.69/5.01  
% 35.69/5.01  --bmc1_incremental                      false
% 35.69/5.01  --bmc1_axioms                           reachable_all
% 35.69/5.01  --bmc1_min_bound                        0
% 35.69/5.01  --bmc1_max_bound                        -1
% 35.69/5.01  --bmc1_max_bound_default                -1
% 35.69/5.01  --bmc1_symbol_reachability              true
% 35.69/5.01  --bmc1_property_lemmas                  false
% 35.69/5.01  --bmc1_k_induction                      false
% 35.69/5.01  --bmc1_non_equiv_states                 false
% 35.69/5.01  --bmc1_deadlock                         false
% 35.69/5.01  --bmc1_ucm                              false
% 35.69/5.01  --bmc1_add_unsat_core                   none
% 35.69/5.01  --bmc1_unsat_core_children              false
% 35.69/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.69/5.01  --bmc1_out_stat                         full
% 35.69/5.01  --bmc1_ground_init                      false
% 35.69/5.01  --bmc1_pre_inst_next_state              false
% 35.69/5.01  --bmc1_pre_inst_state                   false
% 35.69/5.01  --bmc1_pre_inst_reach_state             false
% 35.69/5.01  --bmc1_out_unsat_core                   false
% 35.69/5.01  --bmc1_aig_witness_out                  false
% 35.69/5.01  --bmc1_verbose                          false
% 35.69/5.01  --bmc1_dump_clauses_tptp                false
% 35.69/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.69/5.01  --bmc1_dump_file                        -
% 35.69/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.69/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.69/5.01  --bmc1_ucm_extend_mode                  1
% 35.69/5.01  --bmc1_ucm_init_mode                    2
% 35.69/5.01  --bmc1_ucm_cone_mode                    none
% 35.69/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.69/5.01  --bmc1_ucm_relax_model                  4
% 35.69/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.69/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.69/5.01  --bmc1_ucm_layered_model                none
% 35.69/5.01  --bmc1_ucm_max_lemma_size               10
% 35.69/5.01  
% 35.69/5.01  ------ AIG Options
% 35.69/5.01  
% 35.69/5.01  --aig_mode                              false
% 35.69/5.01  
% 35.69/5.01  ------ Instantiation Options
% 35.69/5.01  
% 35.69/5.01  --instantiation_flag                    true
% 35.69/5.01  --inst_sos_flag                         true
% 35.69/5.01  --inst_sos_phase                        true
% 35.69/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.69/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.69/5.01  --inst_lit_sel_side                     num_symb
% 35.69/5.01  --inst_solver_per_active                1400
% 35.69/5.01  --inst_solver_calls_frac                1.
% 35.69/5.01  --inst_passive_queue_type               priority_queues
% 35.69/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.69/5.01  --inst_passive_queues_freq              [25;2]
% 35.69/5.01  --inst_dismatching                      true
% 35.69/5.01  --inst_eager_unprocessed_to_passive     true
% 35.69/5.01  --inst_prop_sim_given                   true
% 35.69/5.01  --inst_prop_sim_new                     false
% 35.69/5.01  --inst_subs_new                         false
% 35.69/5.01  --inst_eq_res_simp                      false
% 35.69/5.01  --inst_subs_given                       false
% 35.69/5.01  --inst_orphan_elimination               true
% 35.69/5.01  --inst_learning_loop_flag               true
% 35.69/5.01  --inst_learning_start                   3000
% 35.69/5.01  --inst_learning_factor                  2
% 35.69/5.01  --inst_start_prop_sim_after_learn       3
% 35.69/5.01  --inst_sel_renew                        solver
% 35.69/5.01  --inst_lit_activity_flag                true
% 35.69/5.01  --inst_restr_to_given                   false
% 35.69/5.01  --inst_activity_threshold               500
% 35.69/5.01  --inst_out_proof                        true
% 35.69/5.01  
% 35.69/5.01  ------ Resolution Options
% 35.69/5.01  
% 35.69/5.01  --resolution_flag                       true
% 35.69/5.01  --res_lit_sel                           adaptive
% 35.69/5.01  --res_lit_sel_side                      none
% 35.69/5.01  --res_ordering                          kbo
% 35.69/5.01  --res_to_prop_solver                    active
% 35.69/5.01  --res_prop_simpl_new                    false
% 35.69/5.01  --res_prop_simpl_given                  true
% 35.69/5.01  --res_passive_queue_type                priority_queues
% 35.69/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.69/5.01  --res_passive_queues_freq               [15;5]
% 35.69/5.01  --res_forward_subs                      full
% 35.69/5.01  --res_backward_subs                     full
% 35.69/5.01  --res_forward_subs_resolution           true
% 35.69/5.01  --res_backward_subs_resolution          true
% 35.69/5.01  --res_orphan_elimination                true
% 35.69/5.01  --res_time_limit                        2.
% 35.69/5.01  --res_out_proof                         true
% 35.69/5.01  
% 35.69/5.01  ------ Superposition Options
% 35.69/5.01  
% 35.69/5.01  --superposition_flag                    true
% 35.69/5.01  --sup_passive_queue_type                priority_queues
% 35.69/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.69/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.69/5.01  --demod_completeness_check              fast
% 35.69/5.01  --demod_use_ground                      true
% 35.69/5.01  --sup_to_prop_solver                    passive
% 35.69/5.01  --sup_prop_simpl_new                    true
% 35.69/5.01  --sup_prop_simpl_given                  true
% 35.69/5.01  --sup_fun_splitting                     true
% 35.69/5.01  --sup_smt_interval                      50000
% 35.69/5.01  
% 35.69/5.01  ------ Superposition Simplification Setup
% 35.69/5.01  
% 35.69/5.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.69/5.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.69/5.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.69/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.69/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.69/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.69/5.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.69/5.01  --sup_immed_triv                        [TrivRules]
% 35.69/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.69/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.69/5.01  --sup_immed_bw_main                     []
% 35.69/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.69/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.69/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.69/5.01  --sup_input_bw                          []
% 35.69/5.01  
% 35.69/5.01  ------ Combination Options
% 35.69/5.01  
% 35.69/5.01  --comb_res_mult                         3
% 35.69/5.01  --comb_sup_mult                         2
% 35.69/5.01  --comb_inst_mult                        10
% 35.69/5.01  
% 35.69/5.01  ------ Debug Options
% 35.69/5.01  
% 35.69/5.01  --dbg_backtrace                         false
% 35.69/5.01  --dbg_dump_prop_clauses                 false
% 35.69/5.01  --dbg_dump_prop_clauses_file            -
% 35.69/5.01  --dbg_out_stat                          false
% 35.69/5.01  ------ Parsing...
% 35.69/5.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.69/5.01  
% 35.69/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.69/5.01  
% 35.69/5.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.69/5.01  
% 35.69/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.69/5.01  ------ Proving...
% 35.69/5.01  ------ Problem Properties 
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  clauses                                 24
% 35.69/5.01  conjectures                             1
% 35.69/5.01  EPR                                     5
% 35.69/5.01  Horn                                    17
% 35.69/5.01  unary                                   8
% 35.69/5.01  binary                                  11
% 35.69/5.01  lits                                    45
% 35.69/5.01  lits eq                                 14
% 35.69/5.01  fd_pure                                 0
% 35.69/5.01  fd_pseudo                               0
% 35.69/5.01  fd_cond                                 0
% 35.69/5.01  fd_pseudo_cond                          4
% 35.69/5.01  AC symbols                              0
% 35.69/5.01  
% 35.69/5.01  ------ Schedule dynamic 5 is on 
% 35.69/5.01  
% 35.69/5.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  ------ 
% 35.69/5.01  Current options:
% 35.69/5.01  ------ 
% 35.69/5.01  
% 35.69/5.01  ------ Input Options
% 35.69/5.01  
% 35.69/5.01  --out_options                           all
% 35.69/5.01  --tptp_safe_out                         true
% 35.69/5.01  --problem_path                          ""
% 35.69/5.01  --include_path                          ""
% 35.69/5.01  --clausifier                            res/vclausify_rel
% 35.69/5.01  --clausifier_options                    ""
% 35.69/5.01  --stdin                                 false
% 35.69/5.01  --stats_out                             all
% 35.69/5.01  
% 35.69/5.01  ------ General Options
% 35.69/5.01  
% 35.69/5.01  --fof                                   false
% 35.69/5.01  --time_out_real                         305.
% 35.69/5.01  --time_out_virtual                      -1.
% 35.69/5.01  --symbol_type_check                     false
% 35.69/5.01  --clausify_out                          false
% 35.69/5.01  --sig_cnt_out                           false
% 35.69/5.01  --trig_cnt_out                          false
% 35.69/5.01  --trig_cnt_out_tolerance                1.
% 35.69/5.01  --trig_cnt_out_sk_spl                   false
% 35.69/5.01  --abstr_cl_out                          false
% 35.69/5.01  
% 35.69/5.01  ------ Global Options
% 35.69/5.01  
% 35.69/5.01  --schedule                              default
% 35.69/5.01  --add_important_lit                     false
% 35.69/5.01  --prop_solver_per_cl                    1000
% 35.69/5.01  --min_unsat_core                        false
% 35.69/5.01  --soft_assumptions                      false
% 35.69/5.01  --soft_lemma_size                       3
% 35.69/5.01  --prop_impl_unit_size                   0
% 35.69/5.01  --prop_impl_unit                        []
% 35.69/5.01  --share_sel_clauses                     true
% 35.69/5.01  --reset_solvers                         false
% 35.69/5.01  --bc_imp_inh                            [conj_cone]
% 35.69/5.01  --conj_cone_tolerance                   3.
% 35.69/5.01  --extra_neg_conj                        none
% 35.69/5.01  --large_theory_mode                     true
% 35.69/5.01  --prolific_symb_bound                   200
% 35.69/5.01  --lt_threshold                          2000
% 35.69/5.01  --clause_weak_htbl                      true
% 35.69/5.01  --gc_record_bc_elim                     false
% 35.69/5.01  
% 35.69/5.01  ------ Preprocessing Options
% 35.69/5.01  
% 35.69/5.01  --preprocessing_flag                    true
% 35.69/5.01  --time_out_prep_mult                    0.1
% 35.69/5.01  --splitting_mode                        input
% 35.69/5.01  --splitting_grd                         true
% 35.69/5.01  --splitting_cvd                         false
% 35.69/5.01  --splitting_cvd_svl                     false
% 35.69/5.01  --splitting_nvd                         32
% 35.69/5.01  --sub_typing                            true
% 35.69/5.01  --prep_gs_sim                           true
% 35.69/5.01  --prep_unflatten                        true
% 35.69/5.01  --prep_res_sim                          true
% 35.69/5.01  --prep_upred                            true
% 35.69/5.01  --prep_sem_filter                       exhaustive
% 35.69/5.01  --prep_sem_filter_out                   false
% 35.69/5.01  --pred_elim                             true
% 35.69/5.01  --res_sim_input                         true
% 35.69/5.01  --eq_ax_congr_red                       true
% 35.69/5.01  --pure_diseq_elim                       true
% 35.69/5.01  --brand_transform                       false
% 35.69/5.01  --non_eq_to_eq                          false
% 35.69/5.01  --prep_def_merge                        true
% 35.69/5.01  --prep_def_merge_prop_impl              false
% 35.69/5.01  --prep_def_merge_mbd                    true
% 35.69/5.01  --prep_def_merge_tr_red                 false
% 35.69/5.01  --prep_def_merge_tr_cl                  false
% 35.69/5.01  --smt_preprocessing                     true
% 35.69/5.01  --smt_ac_axioms                         fast
% 35.69/5.01  --preprocessed_out                      false
% 35.69/5.01  --preprocessed_stats                    false
% 35.69/5.01  
% 35.69/5.01  ------ Abstraction refinement Options
% 35.69/5.01  
% 35.69/5.01  --abstr_ref                             []
% 35.69/5.01  --abstr_ref_prep                        false
% 35.69/5.01  --abstr_ref_until_sat                   false
% 35.69/5.01  --abstr_ref_sig_restrict                funpre
% 35.69/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.69/5.01  --abstr_ref_under                       []
% 35.69/5.01  
% 35.69/5.01  ------ SAT Options
% 35.69/5.01  
% 35.69/5.01  --sat_mode                              false
% 35.69/5.01  --sat_fm_restart_options                ""
% 35.69/5.01  --sat_gr_def                            false
% 35.69/5.01  --sat_epr_types                         true
% 35.69/5.01  --sat_non_cyclic_types                  false
% 35.69/5.01  --sat_finite_models                     false
% 35.69/5.01  --sat_fm_lemmas                         false
% 35.69/5.01  --sat_fm_prep                           false
% 35.69/5.01  --sat_fm_uc_incr                        true
% 35.69/5.01  --sat_out_model                         small
% 35.69/5.01  --sat_out_clauses                       false
% 35.69/5.01  
% 35.69/5.01  ------ QBF Options
% 35.69/5.01  
% 35.69/5.01  --qbf_mode                              false
% 35.69/5.01  --qbf_elim_univ                         false
% 35.69/5.01  --qbf_dom_inst                          none
% 35.69/5.01  --qbf_dom_pre_inst                      false
% 35.69/5.01  --qbf_sk_in                             false
% 35.69/5.01  --qbf_pred_elim                         true
% 35.69/5.01  --qbf_split                             512
% 35.69/5.01  
% 35.69/5.01  ------ BMC1 Options
% 35.69/5.01  
% 35.69/5.01  --bmc1_incremental                      false
% 35.69/5.01  --bmc1_axioms                           reachable_all
% 35.69/5.01  --bmc1_min_bound                        0
% 35.69/5.01  --bmc1_max_bound                        -1
% 35.69/5.01  --bmc1_max_bound_default                -1
% 35.69/5.01  --bmc1_symbol_reachability              true
% 35.69/5.01  --bmc1_property_lemmas                  false
% 35.69/5.01  --bmc1_k_induction                      false
% 35.69/5.01  --bmc1_non_equiv_states                 false
% 35.69/5.01  --bmc1_deadlock                         false
% 35.69/5.01  --bmc1_ucm                              false
% 35.69/5.01  --bmc1_add_unsat_core                   none
% 35.69/5.01  --bmc1_unsat_core_children              false
% 35.69/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.69/5.01  --bmc1_out_stat                         full
% 35.69/5.01  --bmc1_ground_init                      false
% 35.69/5.01  --bmc1_pre_inst_next_state              false
% 35.69/5.01  --bmc1_pre_inst_state                   false
% 35.69/5.01  --bmc1_pre_inst_reach_state             false
% 35.69/5.01  --bmc1_out_unsat_core                   false
% 35.69/5.01  --bmc1_aig_witness_out                  false
% 35.69/5.01  --bmc1_verbose                          false
% 35.69/5.01  --bmc1_dump_clauses_tptp                false
% 35.69/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.69/5.01  --bmc1_dump_file                        -
% 35.69/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.69/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.69/5.01  --bmc1_ucm_extend_mode                  1
% 35.69/5.01  --bmc1_ucm_init_mode                    2
% 35.69/5.01  --bmc1_ucm_cone_mode                    none
% 35.69/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.69/5.01  --bmc1_ucm_relax_model                  4
% 35.69/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.69/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.69/5.01  --bmc1_ucm_layered_model                none
% 35.69/5.01  --bmc1_ucm_max_lemma_size               10
% 35.69/5.01  
% 35.69/5.01  ------ AIG Options
% 35.69/5.01  
% 35.69/5.01  --aig_mode                              false
% 35.69/5.01  
% 35.69/5.01  ------ Instantiation Options
% 35.69/5.01  
% 35.69/5.01  --instantiation_flag                    true
% 35.69/5.01  --inst_sos_flag                         true
% 35.69/5.01  --inst_sos_phase                        true
% 35.69/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.69/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.69/5.01  --inst_lit_sel_side                     none
% 35.69/5.01  --inst_solver_per_active                1400
% 35.69/5.01  --inst_solver_calls_frac                1.
% 35.69/5.01  --inst_passive_queue_type               priority_queues
% 35.69/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.69/5.01  --inst_passive_queues_freq              [25;2]
% 35.69/5.01  --inst_dismatching                      true
% 35.69/5.01  --inst_eager_unprocessed_to_passive     true
% 35.69/5.01  --inst_prop_sim_given                   true
% 35.69/5.01  --inst_prop_sim_new                     false
% 35.69/5.01  --inst_subs_new                         false
% 35.69/5.01  --inst_eq_res_simp                      false
% 35.69/5.01  --inst_subs_given                       false
% 35.69/5.01  --inst_orphan_elimination               true
% 35.69/5.01  --inst_learning_loop_flag               true
% 35.69/5.01  --inst_learning_start                   3000
% 35.69/5.01  --inst_learning_factor                  2
% 35.69/5.01  --inst_start_prop_sim_after_learn       3
% 35.69/5.01  --inst_sel_renew                        solver
% 35.69/5.01  --inst_lit_activity_flag                true
% 35.69/5.01  --inst_restr_to_given                   false
% 35.69/5.01  --inst_activity_threshold               500
% 35.69/5.01  --inst_out_proof                        true
% 35.69/5.01  
% 35.69/5.01  ------ Resolution Options
% 35.69/5.01  
% 35.69/5.01  --resolution_flag                       false
% 35.69/5.01  --res_lit_sel                           adaptive
% 35.69/5.01  --res_lit_sel_side                      none
% 35.69/5.01  --res_ordering                          kbo
% 35.69/5.01  --res_to_prop_solver                    active
% 35.69/5.01  --res_prop_simpl_new                    false
% 35.69/5.01  --res_prop_simpl_given                  true
% 35.69/5.01  --res_passive_queue_type                priority_queues
% 35.69/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.69/5.01  --res_passive_queues_freq               [15;5]
% 35.69/5.01  --res_forward_subs                      full
% 35.69/5.01  --res_backward_subs                     full
% 35.69/5.01  --res_forward_subs_resolution           true
% 35.69/5.01  --res_backward_subs_resolution          true
% 35.69/5.01  --res_orphan_elimination                true
% 35.69/5.01  --res_time_limit                        2.
% 35.69/5.01  --res_out_proof                         true
% 35.69/5.01  
% 35.69/5.01  ------ Superposition Options
% 35.69/5.01  
% 35.69/5.01  --superposition_flag                    true
% 35.69/5.01  --sup_passive_queue_type                priority_queues
% 35.69/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.69/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.69/5.01  --demod_completeness_check              fast
% 35.69/5.01  --demod_use_ground                      true
% 35.69/5.01  --sup_to_prop_solver                    passive
% 35.69/5.01  --sup_prop_simpl_new                    true
% 35.69/5.01  --sup_prop_simpl_given                  true
% 35.69/5.01  --sup_fun_splitting                     true
% 35.69/5.01  --sup_smt_interval                      50000
% 35.69/5.01  
% 35.69/5.01  ------ Superposition Simplification Setup
% 35.69/5.01  
% 35.69/5.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.69/5.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.69/5.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.69/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.69/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.69/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.69/5.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.69/5.01  --sup_immed_triv                        [TrivRules]
% 35.69/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.69/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.69/5.01  --sup_immed_bw_main                     []
% 35.69/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.69/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.69/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.69/5.01  --sup_input_bw                          []
% 35.69/5.01  
% 35.69/5.01  ------ Combination Options
% 35.69/5.01  
% 35.69/5.01  --comb_res_mult                         3
% 35.69/5.01  --comb_sup_mult                         2
% 35.69/5.01  --comb_inst_mult                        10
% 35.69/5.01  
% 35.69/5.01  ------ Debug Options
% 35.69/5.01  
% 35.69/5.01  --dbg_backtrace                         false
% 35.69/5.01  --dbg_dump_prop_clauses                 false
% 35.69/5.01  --dbg_dump_prop_clauses_file            -
% 35.69/5.01  --dbg_out_stat                          false
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  ------ Proving...
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  % SZS status Theorem for theBenchmark.p
% 35.69/5.01  
% 35.69/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.69/5.01  
% 35.69/5.01  fof(f17,axiom,(
% 35.69/5.01    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f29,plain,(
% 35.69/5.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.69/5.01    inference(ennf_transformation,[],[f17])).
% 35.69/5.01  
% 35.69/5.01  fof(f76,plain,(
% 35.69/5.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f29])).
% 35.69/5.01  
% 35.69/5.01  fof(f11,axiom,(
% 35.69/5.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f70,plain,(
% 35.69/5.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f11])).
% 35.69/5.01  
% 35.69/5.01  fof(f12,axiom,(
% 35.69/5.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f71,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f12])).
% 35.69/5.01  
% 35.69/5.01  fof(f13,axiom,(
% 35.69/5.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f72,plain,(
% 35.69/5.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f13])).
% 35.69/5.01  
% 35.69/5.01  fof(f14,axiom,(
% 35.69/5.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f73,plain,(
% 35.69/5.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f14])).
% 35.69/5.01  
% 35.69/5.01  fof(f15,axiom,(
% 35.69/5.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f74,plain,(
% 35.69/5.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f15])).
% 35.69/5.01  
% 35.69/5.01  fof(f16,axiom,(
% 35.69/5.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f75,plain,(
% 35.69/5.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f16])).
% 35.69/5.01  
% 35.69/5.01  fof(f83,plain,(
% 35.69/5.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f74,f75])).
% 35.69/5.01  
% 35.69/5.01  fof(f84,plain,(
% 35.69/5.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f73,f83])).
% 35.69/5.01  
% 35.69/5.01  fof(f85,plain,(
% 35.69/5.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f72,f84])).
% 35.69/5.01  
% 35.69/5.01  fof(f86,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f71,f85])).
% 35.69/5.01  
% 35.69/5.01  fof(f87,plain,(
% 35.69/5.01    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f70,f86])).
% 35.69/5.01  
% 35.69/5.01  fof(f94,plain,(
% 35.69/5.01    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f76,f87])).
% 35.69/5.01  
% 35.69/5.01  fof(f2,axiom,(
% 35.69/5.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f26,plain,(
% 35.69/5.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 35.69/5.01    inference(ennf_transformation,[],[f2])).
% 35.69/5.01  
% 35.69/5.01  fof(f32,plain,(
% 35.69/5.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 35.69/5.01    inference(nnf_transformation,[],[f26])).
% 35.69/5.01  
% 35.69/5.01  fof(f33,plain,(
% 35.69/5.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.69/5.01    inference(rectify,[],[f32])).
% 35.69/5.01  
% 35.69/5.01  fof(f34,plain,(
% 35.69/5.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 35.69/5.01    introduced(choice_axiom,[])).
% 35.69/5.01  
% 35.69/5.01  fof(f35,plain,(
% 35.69/5.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.69/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 35.69/5.01  
% 35.69/5.01  fof(f51,plain,(
% 35.69/5.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f35])).
% 35.69/5.01  
% 35.69/5.01  fof(f4,axiom,(
% 35.69/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f25,plain,(
% 35.69/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.69/5.01    inference(rectify,[],[f4])).
% 35.69/5.01  
% 35.69/5.01  fof(f28,plain,(
% 35.69/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.69/5.01    inference(ennf_transformation,[],[f25])).
% 35.69/5.01  
% 35.69/5.01  fof(f38,plain,(
% 35.69/5.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 35.69/5.01    introduced(choice_axiom,[])).
% 35.69/5.01  
% 35.69/5.01  fof(f39,plain,(
% 35.69/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.69/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f38])).
% 35.69/5.01  
% 35.69/5.01  fof(f57,plain,(
% 35.69/5.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.69/5.01    inference(cnf_transformation,[],[f39])).
% 35.69/5.01  
% 35.69/5.01  fof(f10,axiom,(
% 35.69/5.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f43,plain,(
% 35.69/5.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 35.69/5.01    inference(nnf_transformation,[],[f10])).
% 35.69/5.01  
% 35.69/5.01  fof(f44,plain,(
% 35.69/5.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 35.69/5.01    inference(rectify,[],[f43])).
% 35.69/5.01  
% 35.69/5.01  fof(f45,plain,(
% 35.69/5.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 35.69/5.01    introduced(choice_axiom,[])).
% 35.69/5.01  
% 35.69/5.01  fof(f46,plain,(
% 35.69/5.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 35.69/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 35.69/5.01  
% 35.69/5.01  fof(f67,plain,(
% 35.69/5.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 35.69/5.01    inference(cnf_transformation,[],[f46])).
% 35.69/5.01  
% 35.69/5.01  fof(f92,plain,(
% 35.69/5.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 35.69/5.01    inference(definition_unfolding,[],[f67,f87])).
% 35.69/5.01  
% 35.69/5.01  fof(f102,plain,(
% 35.69/5.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 35.69/5.01    inference(equality_resolution,[],[f92])).
% 35.69/5.01  
% 35.69/5.01  fof(f103,plain,(
% 35.69/5.01    ( ! [X3] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) )),
% 35.69/5.01    inference(equality_resolution,[],[f102])).
% 35.69/5.01  
% 35.69/5.01  fof(f8,axiom,(
% 35.69/5.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f64,plain,(
% 35.69/5.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f8])).
% 35.69/5.01  
% 35.69/5.01  fof(f56,plain,(
% 35.69/5.01    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f39])).
% 35.69/5.01  
% 35.69/5.01  fof(f1,axiom,(
% 35.69/5.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f49,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f1])).
% 35.69/5.01  
% 35.69/5.01  fof(f3,axiom,(
% 35.69/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f24,plain,(
% 35.69/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.69/5.01    inference(rectify,[],[f3])).
% 35.69/5.01  
% 35.69/5.01  fof(f27,plain,(
% 35.69/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 35.69/5.01    inference(ennf_transformation,[],[f24])).
% 35.69/5.01  
% 35.69/5.01  fof(f36,plain,(
% 35.69/5.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 35.69/5.01    introduced(choice_axiom,[])).
% 35.69/5.01  
% 35.69/5.01  fof(f37,plain,(
% 35.69/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 35.69/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f36])).
% 35.69/5.01  
% 35.69/5.01  fof(f55,plain,(
% 35.69/5.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f37])).
% 35.69/5.01  
% 35.69/5.01  fof(f5,axiom,(
% 35.69/5.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f40,plain,(
% 35.69/5.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.69/5.01    inference(nnf_transformation,[],[f5])).
% 35.69/5.01  
% 35.69/5.01  fof(f41,plain,(
% 35.69/5.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.69/5.01    inference(flattening,[],[f40])).
% 35.69/5.01  
% 35.69/5.01  fof(f60,plain,(
% 35.69/5.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f41])).
% 35.69/5.01  
% 35.69/5.01  fof(f66,plain,(
% 35.69/5.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 35.69/5.01    inference(cnf_transformation,[],[f46])).
% 35.69/5.01  
% 35.69/5.01  fof(f93,plain,(
% 35.69/5.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 35.69/5.01    inference(definition_unfolding,[],[f66,f87])).
% 35.69/5.01  
% 35.69/5.01  fof(f104,plain,(
% 35.69/5.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 35.69/5.01    inference(equality_resolution,[],[f93])).
% 35.69/5.01  
% 35.69/5.01  fof(f18,axiom,(
% 35.69/5.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f77,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.69/5.01    inference(cnf_transformation,[],[f18])).
% 35.69/5.01  
% 35.69/5.01  fof(f9,axiom,(
% 35.69/5.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f65,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f9])).
% 35.69/5.01  
% 35.69/5.01  fof(f7,axiom,(
% 35.69/5.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f63,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.69/5.01    inference(cnf_transformation,[],[f7])).
% 35.69/5.01  
% 35.69/5.01  fof(f82,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f65,f63])).
% 35.69/5.01  
% 35.69/5.01  fof(f95,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 35.69/5.01    inference(definition_unfolding,[],[f77,f82,f86])).
% 35.69/5.01  
% 35.69/5.01  fof(f22,conjecture,(
% 35.69/5.01    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f23,negated_conjecture,(
% 35.69/5.01    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 35.69/5.01    inference(negated_conjecture,[],[f22])).
% 35.69/5.01  
% 35.69/5.01  fof(f31,plain,(
% 35.69/5.01    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 35.69/5.01    inference(ennf_transformation,[],[f23])).
% 35.69/5.01  
% 35.69/5.01  fof(f47,plain,(
% 35.69/5.01    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK4,sK5) != k3_tarski(k2_tarski(k1_tarski(sK4),k1_tarski(sK5)))),
% 35.69/5.01    introduced(choice_axiom,[])).
% 35.69/5.01  
% 35.69/5.01  fof(f48,plain,(
% 35.69/5.01    k2_tarski(sK4,sK5) != k3_tarski(k2_tarski(k1_tarski(sK4),k1_tarski(sK5)))),
% 35.69/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f47])).
% 35.69/5.01  
% 35.69/5.01  fof(f81,plain,(
% 35.69/5.01    k2_tarski(sK4,sK5) != k3_tarski(k2_tarski(k1_tarski(sK4),k1_tarski(sK5)))),
% 35.69/5.01    inference(cnf_transformation,[],[f48])).
% 35.69/5.01  
% 35.69/5.01  fof(f99,plain,(
% 35.69/5.01    k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),
% 35.69/5.01    inference(definition_unfolding,[],[f81,f86,f86,f87,f87])).
% 35.69/5.01  
% 35.69/5.01  fof(f21,axiom,(
% 35.69/5.01    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f80,plain,(
% 35.69/5.01    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 35.69/5.01    inference(cnf_transformation,[],[f21])).
% 35.69/5.01  
% 35.69/5.01  fof(f98,plain,(
% 35.69/5.01    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 35.69/5.01    inference(definition_unfolding,[],[f80,f87])).
% 35.69/5.01  
% 35.69/5.01  fof(f58,plain,(
% 35.69/5.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.69/5.01    inference(cnf_transformation,[],[f41])).
% 35.69/5.01  
% 35.69/5.01  fof(f101,plain,(
% 35.69/5.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.69/5.01    inference(equality_resolution,[],[f58])).
% 35.69/5.01  
% 35.69/5.01  fof(f6,axiom,(
% 35.69/5.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f42,plain,(
% 35.69/5.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 35.69/5.01    inference(nnf_transformation,[],[f6])).
% 35.69/5.01  
% 35.69/5.01  fof(f62,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f42])).
% 35.69/5.01  
% 35.69/5.01  fof(f88,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 35.69/5.01    inference(definition_unfolding,[],[f62,f63])).
% 35.69/5.01  
% 35.69/5.01  fof(f20,axiom,(
% 35.69/5.01    ! [X0,X1] : (X0 != X1 => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1))),
% 35.69/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.69/5.01  
% 35.69/5.01  fof(f30,plain,(
% 35.69/5.01    ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1)),
% 35.69/5.01    inference(ennf_transformation,[],[f20])).
% 35.69/5.01  
% 35.69/5.01  fof(f79,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1) )),
% 35.69/5.01    inference(cnf_transformation,[],[f30])).
% 35.69/5.01  
% 35.69/5.01  fof(f97,plain,(
% 35.69/5.01    ( ! [X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) | X0 = X1) )),
% 35.69/5.01    inference(definition_unfolding,[],[f79,f87,f87,f86])).
% 35.69/5.01  
% 35.69/5.01  cnf(c_19,plain,
% 35.69/5.01      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
% 35.69/5.01      | r2_hidden(X0,X1) ),
% 35.69/5.01      inference(cnf_transformation,[],[f94]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1163,plain,
% 35.69/5.01      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 35.69/5.01      | r2_hidden(X0,X1) = iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2,plain,
% 35.69/5.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 35.69/5.01      inference(cnf_transformation,[],[f51]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1179,plain,
% 35.69/5.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 35.69/5.01      | r1_tarski(X0,X1) = iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_7,plain,
% 35.69/5.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 35.69/5.01      inference(cnf_transformation,[],[f57]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1174,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.69/5.01      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2248,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.69/5.01      | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1179,c_1174]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_17,plain,
% 35.69/5.01      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 35.69/5.01      inference(cnf_transformation,[],[f103]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1165,plain,
% 35.69/5.01      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_14,plain,
% 35.69/5.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 35.69/5.01      inference(cnf_transformation,[],[f64]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1168,plain,
% 35.69/5.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_8,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
% 35.69/5.01      inference(cnf_transformation,[],[f56]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1173,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) = iProver_top
% 35.69/5.01      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_0,plain,
% 35.69/5.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.69/5.01      inference(cnf_transformation,[],[f49]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2005,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.69/5.01      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_0,c_1174]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2294,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.69/5.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1173,c_2005]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2463,plain,
% 35.69/5.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1168,c_2294]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_4,plain,
% 35.69/5.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 35.69/5.01      inference(cnf_transformation,[],[f55]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1177,plain,
% 35.69/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.69/5.01      | r2_hidden(X2,X1) != iProver_top
% 35.69/5.01      | r2_hidden(X2,X0) != iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_3898,plain,
% 35.69/5.01      ( r2_hidden(X0,X1) != iProver_top
% 35.69/5.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_2463,c_1177]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_3955,plain,
% 35.69/5.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1165,c_3898]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_3961,plain,
% 35.69/5.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1179,c_3955]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_9,plain,
% 35.69/5.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 35.69/5.01      inference(cnf_transformation,[],[f60]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1172,plain,
% 35.69/5.01      ( X0 = X1
% 35.69/5.01      | r1_tarski(X1,X0) != iProver_top
% 35.69/5.01      | r1_tarski(X0,X1) != iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_4069,plain,
% 35.69/5.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_3961,c_1172]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_4255,plain,
% 35.69/5.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 35.69/5.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_2248,c_4069]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_4951,plain,
% 35.69/5.01      ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
% 35.69/5.01      | r2_hidden(X0,X1) = iProver_top ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1163,c_4255]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_18,plain,
% 35.69/5.01      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 35.69/5.01      inference(cnf_transformation,[],[f104]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1164,plain,
% 35.69/5.01      ( X0 = X1
% 35.69/5.01      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_6290,plain,
% 35.69/5.01      ( X0 = X1
% 35.69/5.01      | k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k1_xboole_0 ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_4951,c_1164]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_20,plain,
% 35.69/5.01      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 35.69/5.01      inference(cnf_transformation,[],[f95]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_24,negated_conjecture,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 35.69/5.01      inference(cnf_transformation,[],[f99]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1564,plain,
% 35.69/5.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 35.69/5.01      inference(demodulation,[status(thm)],[c_20,c_24]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1738,plain,
% 35.69/5.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_0,c_1564]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_50132,plain,
% 35.69/5.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0)) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
% 35.69/5.01      | sK5 = sK4 ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_6290,c_1738]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_23,plain,
% 35.69/5.01      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 35.69/5.01      inference(cnf_transformation,[],[f98]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1568,plain,
% 35.69/5.01      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_20,c_23]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_11,plain,
% 35.69/5.01      ( r1_tarski(X0,X0) ),
% 35.69/5.01      inference(cnf_transformation,[],[f101]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1171,plain,
% 35.69/5.01      ( r1_tarski(X0,X0) = iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_12,plain,
% 35.69/5.01      ( ~ r1_tarski(X0,X1)
% 35.69/5.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.69/5.01      inference(cnf_transformation,[],[f88]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1170,plain,
% 35.69/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 35.69/5.01      | r1_tarski(X0,X1) != iProver_top ),
% 35.69/5.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1503,plain,
% 35.69/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 35.69/5.01      inference(superposition,[status(thm)],[c_1171,c_1170]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1569,plain,
% 35.69/5.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.69/5.01      inference(light_normalisation,[status(thm)],[c_1568,c_1503]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_50288,plain,
% 35.69/5.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
% 35.69/5.01      | sK5 = sK4 ),
% 35.69/5.01      inference(demodulation,[status(thm)],[c_50132,c_1569]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_726,plain,
% 35.69/5.01      ( X0 != X1
% 35.69/5.01      | X2 != X3
% 35.69/5.01      | X4 != X5
% 35.69/5.01      | X6 != X7
% 35.69/5.01      | X8 != X9
% 35.69/5.01      | X10 != X11
% 35.69/5.01      | X12 != X13
% 35.69/5.01      | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
% 35.69/5.01      theory(equality) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_35049,plain,
% 35.69/5.01      ( k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_726]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1439,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
% 35.69/5.01      | sK5 != X6
% 35.69/5.01      | sK4 != X0
% 35.69/5.01      | sK4 != X1
% 35.69/5.01      | sK4 != X2
% 35.69/5.01      | sK4 != X3
% 35.69/5.01      | sK4 != X4
% 35.69/5.01      | sK4 != X5 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_726]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1908,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(X0,X1,X2,X3,X4,X5,sK5)
% 35.69/5.01      | sK5 != sK5
% 35.69/5.01      | sK4 != X0
% 35.69/5.01      | sK4 != X1
% 35.69/5.01      | sK4 != X2
% 35.69/5.01      | sK4 != X3
% 35.69/5.01      | sK4 != X4
% 35.69/5.01      | sK4 != X5 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1439]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_32070,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 35.69/5.01      | sK5 != sK5
% 35.69/5.01      | sK4 != sK5 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1908]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_721,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_17842,plain,
% 35.69/5.01      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_721]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_17843,plain,
% 35.69/5.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_17842]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_727,plain,
% 35.69/5.01      ( X0 != X1 | k3_tarski(X0) = k3_tarski(X1) ),
% 35.69/5.01      theory(equality) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_9525,plain,
% 35.69/5.01      ( k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_727]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1305,plain,
% 35.69/5.01      ( X0 != X1
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != X1
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = X0 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_721]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1730,plain,
% 35.69/5.01      ( X0 != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = X0
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1305]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_4000,plain,
% 35.69/5.01      ( k3_tarski(X0) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(X0)
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1730]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_8772,plain,
% 35.69/5.01      ( k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_4000]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_6884,plain,
% 35.69/5.01      ( r1_tarski(sK5,sK5) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_11]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1902,plain,
% 35.69/5.01      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_5765,plain,
% 35.69/5.01      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1902]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1207,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != X0
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != X0 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_721]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1308,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(X0)
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(X0) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1207]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_3472,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)))
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1308]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2258,plain,
% 35.69/5.01      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_11]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_2027,plain,
% 35.69/5.01      ( k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_23]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_22,plain,
% 35.69/5.01      ( X0 = X1
% 35.69/5.01      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
% 35.69/5.01      inference(cnf_transformation,[],[f97]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1895,plain,
% 35.69/5.01      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k5_enumset1(X0,X0,X0,X0,X0,X0,sK5)
% 35.69/5.01      | sK5 = X0 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_22]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1901,plain,
% 35.69/5.01      ( k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
% 35.69/5.01      | sK5 = sK4 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1895]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1300,plain,
% 35.69/5.01      ( ~ r1_tarski(X0,k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 35.69/5.01      | ~ r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),X0)
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = X0 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1680,plain,
% 35.69/5.01      ( ~ r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1300]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1247,plain,
% 35.69/5.01      ( X0 != X1
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != X1
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = X0 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_721]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1459,plain,
% 35.69/5.01      ( X0 != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = X0
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1247]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1605,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)
% 35.69/5.01      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)))
% 35.69/5.01      | k3_tarski(k5_enumset1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1459]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1440,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 35.69/5.01      | sK5 != sK4
% 35.69/5.01      | sK4 != sK4 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_1439]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_720,plain,( X0 = X0 ),theory(equality) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_1278,plain,
% 35.69/5.01      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_720]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_38,plain,
% 35.69/5.01      ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_17]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(c_35,plain,
% 35.69/5.01      ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.69/5.01      | sK4 = sK4 ),
% 35.69/5.01      inference(instantiation,[status(thm)],[c_18]) ).
% 35.69/5.01  
% 35.69/5.01  cnf(contradiction,plain,
% 35.69/5.01      ( $false ),
% 35.69/5.01      inference(minisat,
% 35.69/5.01                [status(thm)],
% 35.69/5.01                [c_50288,c_35049,c_32070,c_17843,c_9525,c_8772,c_6884,
% 35.69/5.01                 c_5765,c_3472,c_2258,c_2027,c_1901,c_1680,c_1605,c_1440,
% 35.69/5.01                 c_1278,c_38,c_35,c_24]) ).
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.69/5.01  
% 35.69/5.01  ------                               Statistics
% 35.69/5.01  
% 35.69/5.01  ------ General
% 35.69/5.01  
% 35.69/5.01  abstr_ref_over_cycles:                  0
% 35.69/5.01  abstr_ref_under_cycles:                 0
% 35.69/5.01  gc_basic_clause_elim:                   0
% 35.69/5.01  forced_gc_time:                         0
% 35.69/5.01  parsing_time:                           0.008
% 35.69/5.01  unif_index_cands_time:                  0.
% 35.69/5.01  unif_index_add_time:                    0.
% 35.69/5.01  orderings_time:                         0.
% 35.69/5.01  out_proof_time:                         0.014
% 35.69/5.01  total_time:                             4.306
% 35.69/5.01  num_of_symbols:                         45
% 35.69/5.01  num_of_terms:                           28055
% 35.69/5.01  
% 35.69/5.01  ------ Preprocessing
% 35.69/5.01  
% 35.69/5.01  num_of_splits:                          0
% 35.69/5.01  num_of_split_atoms:                     0
% 35.69/5.01  num_of_reused_defs:                     0
% 35.69/5.01  num_eq_ax_congr_red:                    30
% 35.69/5.01  num_of_sem_filtered_clauses:            1
% 35.69/5.01  num_of_subtypes:                        0
% 35.69/5.01  monotx_restored_types:                  0
% 35.69/5.01  sat_num_of_epr_types:                   0
% 35.69/5.01  sat_num_of_non_cyclic_types:            0
% 35.69/5.01  sat_guarded_non_collapsed_types:        0
% 35.69/5.01  num_pure_diseq_elim:                    0
% 35.69/5.01  simp_replaced_by:                       0
% 35.69/5.01  res_preprocessed:                       113
% 35.69/5.01  prep_upred:                             0
% 35.69/5.01  prep_unflattend:                        16
% 35.69/5.01  smt_new_axioms:                         0
% 35.69/5.01  pred_elim_cands:                        3
% 35.69/5.01  pred_elim:                              0
% 35.69/5.01  pred_elim_cl:                           0
% 35.69/5.01  pred_elim_cycles:                       2
% 35.69/5.01  merged_defs:                            8
% 35.69/5.01  merged_defs_ncl:                        0
% 35.69/5.01  bin_hyper_res:                          8
% 35.69/5.01  prep_cycles:                            4
% 35.69/5.01  pred_elim_time:                         0.002
% 35.69/5.01  splitting_time:                         0.
% 35.69/5.01  sem_filter_time:                        0.
% 35.69/5.01  monotx_time:                            0.
% 35.69/5.01  subtype_inf_time:                       0.
% 35.69/5.01  
% 35.69/5.01  ------ Problem properties
% 35.69/5.01  
% 35.69/5.01  clauses:                                24
% 35.69/5.01  conjectures:                            1
% 35.69/5.01  epr:                                    5
% 35.69/5.01  horn:                                   17
% 35.69/5.01  ground:                                 1
% 35.69/5.01  unary:                                  8
% 35.69/5.01  binary:                                 11
% 35.69/5.01  lits:                                   45
% 35.69/5.01  lits_eq:                                14
% 35.69/5.01  fd_pure:                                0
% 35.69/5.01  fd_pseudo:                              0
% 35.69/5.01  fd_cond:                                0
% 35.69/5.01  fd_pseudo_cond:                         4
% 35.69/5.01  ac_symbols:                             0
% 35.69/5.01  
% 35.69/5.01  ------ Propositional Solver
% 35.69/5.01  
% 35.69/5.01  prop_solver_calls:                      31
% 35.69/5.01  prop_fast_solver_calls:                 2054
% 35.69/5.01  smt_solver_calls:                       0
% 35.69/5.01  smt_fast_solver_calls:                  0
% 35.69/5.01  prop_num_of_clauses:                    14285
% 35.69/5.01  prop_preprocess_simplified:             26028
% 35.69/5.01  prop_fo_subsumed:                       8
% 35.69/5.01  prop_solver_time:                       0.
% 35.69/5.01  smt_solver_time:                        0.
% 35.69/5.01  smt_fast_solver_time:                   0.
% 35.69/5.01  prop_fast_solver_time:                  0.
% 35.69/5.01  prop_unsat_core_time:                   0.001
% 35.69/5.01  
% 35.69/5.01  ------ QBF
% 35.69/5.01  
% 35.69/5.01  qbf_q_res:                              0
% 35.69/5.01  qbf_num_tautologies:                    0
% 35.69/5.01  qbf_prep_cycles:                        0
% 35.69/5.01  
% 35.69/5.01  ------ BMC1
% 35.69/5.01  
% 35.69/5.01  bmc1_current_bound:                     -1
% 35.69/5.01  bmc1_last_solved_bound:                 -1
% 35.69/5.01  bmc1_unsat_core_size:                   -1
% 35.69/5.01  bmc1_unsat_core_parents_size:           -1
% 35.69/5.01  bmc1_merge_next_fun:                    0
% 35.69/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.69/5.01  
% 35.69/5.01  ------ Instantiation
% 35.69/5.01  
% 35.69/5.01  inst_num_of_clauses:                    3613
% 35.69/5.01  inst_num_in_passive:                    1712
% 35.69/5.01  inst_num_in_active:                     1161
% 35.69/5.01  inst_num_in_unprocessed:                741
% 35.69/5.01  inst_num_of_loops:                      1840
% 35.69/5.01  inst_num_of_learning_restarts:          0
% 35.69/5.01  inst_num_moves_active_passive:          677
% 35.69/5.01  inst_lit_activity:                      0
% 35.69/5.01  inst_lit_activity_moves:                0
% 35.69/5.01  inst_num_tautologies:                   0
% 35.69/5.01  inst_num_prop_implied:                  0
% 35.69/5.01  inst_num_existing_simplified:           0
% 35.69/5.01  inst_num_eq_res_simplified:             0
% 35.69/5.01  inst_num_child_elim:                    0
% 35.69/5.01  inst_num_of_dismatching_blockings:      4193
% 35.69/5.01  inst_num_of_non_proper_insts:           6018
% 35.69/5.01  inst_num_of_duplicates:                 0
% 35.69/5.01  inst_inst_num_from_inst_to_res:         0
% 35.69/5.01  inst_dismatching_checking_time:         0.
% 35.69/5.01  
% 35.69/5.01  ------ Resolution
% 35.69/5.01  
% 35.69/5.01  res_num_of_clauses:                     0
% 35.69/5.01  res_num_in_passive:                     0
% 35.69/5.01  res_num_in_active:                      0
% 35.69/5.01  res_num_of_loops:                       117
% 35.69/5.01  res_forward_subset_subsumed:            654
% 35.69/5.01  res_backward_subset_subsumed:           2
% 35.69/5.01  res_forward_subsumed:                   0
% 35.69/5.01  res_backward_subsumed:                  0
% 35.69/5.01  res_forward_subsumption_resolution:     0
% 35.69/5.01  res_backward_subsumption_resolution:    0
% 35.69/5.01  res_clause_to_clause_subsumption:       47645
% 35.69/5.01  res_orphan_elimination:                 0
% 35.69/5.01  res_tautology_del:                      348
% 35.69/5.01  res_num_eq_res_simplified:              0
% 35.69/5.01  res_num_sel_changes:                    0
% 35.69/5.01  res_moves_from_active_to_pass:          0
% 35.69/5.01  
% 35.69/5.01  ------ Superposition
% 35.69/5.01  
% 35.69/5.01  sup_time_total:                         0.
% 35.69/5.01  sup_time_generating:                    0.
% 35.69/5.01  sup_time_sim_full:                      0.
% 35.69/5.01  sup_time_sim_immed:                     0.
% 35.69/5.01  
% 35.69/5.01  sup_num_of_clauses:                     2963
% 35.69/5.01  sup_num_in_active:                      351
% 35.69/5.01  sup_num_in_passive:                     2612
% 35.69/5.01  sup_num_of_loops:                       367
% 35.69/5.01  sup_fw_superposition:                   12568
% 35.69/5.01  sup_bw_superposition:                   6197
% 35.69/5.01  sup_immediate_simplified:               2749
% 35.69/5.01  sup_given_eliminated:                   1
% 35.69/5.01  comparisons_done:                       0
% 35.69/5.01  comparisons_avoided:                    294
% 35.69/5.01  
% 35.69/5.01  ------ Simplifications
% 35.69/5.01  
% 35.69/5.01  
% 35.69/5.01  sim_fw_subset_subsumed:                 60
% 35.69/5.01  sim_bw_subset_subsumed:                 16
% 35.69/5.01  sim_fw_subsumed:                        1802
% 35.69/5.01  sim_bw_subsumed:                        398
% 35.69/5.01  sim_fw_subsumption_res:                 0
% 35.69/5.01  sim_bw_subsumption_res:                 0
% 35.69/5.01  sim_tautology_del:                      9
% 35.69/5.01  sim_eq_tautology_del:                   5289
% 35.69/5.01  sim_eq_res_simp:                        0
% 35.69/5.01  sim_fw_demodulated:                     469
% 35.69/5.01  sim_bw_demodulated:                     16
% 35.69/5.01  sim_light_normalised:                   83
% 35.69/5.01  sim_joinable_taut:                      0
% 35.69/5.01  sim_joinable_simp:                      0
% 35.69/5.01  sim_ac_normalised:                      0
% 35.69/5.01  sim_smt_subsumption:                    0
% 35.69/5.01  
%------------------------------------------------------------------------------
