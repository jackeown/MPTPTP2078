%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:53 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  124 (7291 expanded)
%              Number of clauses        :   64 (1713 expanded)
%              Number of leaves         :   18 (1994 expanded)
%              Depth                    :   31
%              Number of atoms          :  294 (13328 expanded)
%              Number of equality atoms :  124 (7075 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f57,f53,f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

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
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

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
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f35])).

fof(f63,plain,(
    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f64,f65])).

fof(f79,plain,(
    k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK3)))) ),
    inference(definition_unfolding,[],[f63,f65,f66])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1100,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_20])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_452,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_795,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_19])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_441,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2847,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_441])).

cnf(c_4466,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_2847])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_439,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4567,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_4466,c_439])).

cnf(c_4568,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4567,c_19])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1293,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1100,c_21])).

cnf(c_4572,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_4568,c_1293])).

cnf(c_5295,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1100,c_4572])).

cnf(c_1288,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1100,c_16])).

cnf(c_5309,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5295,c_1288])).

cnf(c_5301,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X0),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4572,c_20])).

cnf(c_5463,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)),k3_xboole_0(X0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5301,c_4572])).

cnf(c_5464,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5463,c_1288,c_5309])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_446,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6177,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5464,c_446])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_453,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8705,plain,
    ( r2_hidden(sK0(X0,k3_xboole_0(X1,X1)),X1) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6177,c_453])).

cnf(c_17871,plain,
    ( r1_tarski(X0,k3_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_8705])).

cnf(c_17918,plain,
    ( r1_tarski(k3_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_17871])).

cnf(c_18026,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_17918,c_439])).

cnf(c_5324,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_5309,c_4572])).

cnf(c_5720,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_20,c_5324])).

cnf(c_5735,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_5720,c_1288])).

cnf(c_19304,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k3_xboole_0(k3_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_18026,c_5735])).

cnf(c_1294,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1100,c_21])).

cnf(c_5907,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1294,c_5324])).

cnf(c_5920,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,X0))) = k3_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_5907,c_1288])).

cnf(c_7775,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X1)),k5_xboole_0(X0,k3_xboole_0(X1,X1))) = k5_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_5920,c_4572])).

cnf(c_5721,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_21,c_5324])).

cnf(c_12006,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X1)),k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X0),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_7775,c_5721])).

cnf(c_19369,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)),k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)))),k3_xboole_0(X0,X0)) = k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_18026,c_12006])).

cnf(c_19385,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_19369,c_1100,c_5309])).

cnf(c_19386,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_19385,c_4568])).

cnf(c_19462,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_19304,c_19386])).

cnf(c_19463,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_19462,c_5309])).

cnf(c_1107,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_20])).

cnf(c_5865,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1107,c_5324])).

cnf(c_5873,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_5865,c_1288])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_537,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k1_tarski(sK3)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(demodulation,[status(thm)],[c_1,c_22])).

cnf(c_672,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(superposition,[status(thm)],[c_1,c_537])).

cnf(c_1074,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(demodulation,[status(thm)],[c_21,c_672])).

cnf(c_1430,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(superposition,[status(thm)],[c_21,c_1074])).

cnf(c_6876,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK3)))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(demodulation,[status(thm)],[c_5873,c_1430])).

cnf(c_19817,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK3))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(demodulation,[status(thm)],[c_19463,c_6876])).

cnf(c_7759,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_21,c_5920])).

cnf(c_19838,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_19463,c_7759])).

cnf(c_19841,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_19838,c_19463])).

cnf(c_19850,plain,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
    inference(demodulation,[status(thm)],[c_19817,c_19841])).

cnf(c_19851,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19850])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.36/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.36/1.50  
% 7.36/1.50  ------  iProver source info
% 7.36/1.50  
% 7.36/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.36/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.36/1.50  git: non_committed_changes: false
% 7.36/1.50  git: last_make_outside_of_git: false
% 7.36/1.50  
% 7.36/1.50  ------ 
% 7.36/1.50  
% 7.36/1.50  ------ Input Options
% 7.36/1.50  
% 7.36/1.50  --out_options                           all
% 7.36/1.50  --tptp_safe_out                         true
% 7.36/1.50  --problem_path                          ""
% 7.36/1.50  --include_path                          ""
% 7.36/1.50  --clausifier                            res/vclausify_rel
% 7.36/1.50  --clausifier_options                    ""
% 7.36/1.50  --stdin                                 false
% 7.36/1.50  --stats_out                             all
% 7.36/1.50  
% 7.36/1.50  ------ General Options
% 7.36/1.50  
% 7.36/1.50  --fof                                   false
% 7.36/1.50  --time_out_real                         305.
% 7.36/1.50  --time_out_virtual                      -1.
% 7.36/1.50  --symbol_type_check                     false
% 7.36/1.50  --clausify_out                          false
% 7.36/1.50  --sig_cnt_out                           false
% 7.36/1.50  --trig_cnt_out                          false
% 7.36/1.50  --trig_cnt_out_tolerance                1.
% 7.36/1.50  --trig_cnt_out_sk_spl                   false
% 7.36/1.50  --abstr_cl_out                          false
% 7.36/1.50  
% 7.36/1.50  ------ Global Options
% 7.36/1.50  
% 7.36/1.50  --schedule                              default
% 7.36/1.50  --add_important_lit                     false
% 7.36/1.50  --prop_solver_per_cl                    1000
% 7.36/1.50  --min_unsat_core                        false
% 7.36/1.50  --soft_assumptions                      false
% 7.36/1.50  --soft_lemma_size                       3
% 7.36/1.50  --prop_impl_unit_size                   0
% 7.36/1.50  --prop_impl_unit                        []
% 7.36/1.50  --share_sel_clauses                     true
% 7.36/1.50  --reset_solvers                         false
% 7.36/1.50  --bc_imp_inh                            [conj_cone]
% 7.36/1.50  --conj_cone_tolerance                   3.
% 7.36/1.50  --extra_neg_conj                        none
% 7.36/1.50  --large_theory_mode                     true
% 7.36/1.50  --prolific_symb_bound                   200
% 7.36/1.50  --lt_threshold                          2000
% 7.36/1.50  --clause_weak_htbl                      true
% 7.36/1.50  --gc_record_bc_elim                     false
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing Options
% 7.36/1.50  
% 7.36/1.50  --preprocessing_flag                    true
% 7.36/1.50  --time_out_prep_mult                    0.1
% 7.36/1.50  --splitting_mode                        input
% 7.36/1.50  --splitting_grd                         true
% 7.36/1.50  --splitting_cvd                         false
% 7.36/1.50  --splitting_cvd_svl                     false
% 7.36/1.50  --splitting_nvd                         32
% 7.36/1.50  --sub_typing                            true
% 7.36/1.50  --prep_gs_sim                           true
% 7.36/1.50  --prep_unflatten                        true
% 7.36/1.50  --prep_res_sim                          true
% 7.36/1.50  --prep_upred                            true
% 7.36/1.50  --prep_sem_filter                       exhaustive
% 7.36/1.50  --prep_sem_filter_out                   false
% 7.36/1.50  --pred_elim                             true
% 7.36/1.50  --res_sim_input                         true
% 7.36/1.50  --eq_ax_congr_red                       true
% 7.36/1.50  --pure_diseq_elim                       true
% 7.36/1.50  --brand_transform                       false
% 7.36/1.50  --non_eq_to_eq                          false
% 7.36/1.50  --prep_def_merge                        true
% 7.36/1.50  --prep_def_merge_prop_impl              false
% 7.36/1.50  --prep_def_merge_mbd                    true
% 7.36/1.50  --prep_def_merge_tr_red                 false
% 7.36/1.50  --prep_def_merge_tr_cl                  false
% 7.36/1.50  --smt_preprocessing                     true
% 7.36/1.50  --smt_ac_axioms                         fast
% 7.36/1.50  --preprocessed_out                      false
% 7.36/1.50  --preprocessed_stats                    false
% 7.36/1.50  
% 7.36/1.50  ------ Abstraction refinement Options
% 7.36/1.50  
% 7.36/1.50  --abstr_ref                             []
% 7.36/1.50  --abstr_ref_prep                        false
% 7.36/1.50  --abstr_ref_until_sat                   false
% 7.36/1.50  --abstr_ref_sig_restrict                funpre
% 7.36/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.50  --abstr_ref_under                       []
% 7.36/1.50  
% 7.36/1.50  ------ SAT Options
% 7.36/1.50  
% 7.36/1.50  --sat_mode                              false
% 7.36/1.50  --sat_fm_restart_options                ""
% 7.36/1.50  --sat_gr_def                            false
% 7.36/1.50  --sat_epr_types                         true
% 7.36/1.50  --sat_non_cyclic_types                  false
% 7.36/1.50  --sat_finite_models                     false
% 7.36/1.50  --sat_fm_lemmas                         false
% 7.36/1.50  --sat_fm_prep                           false
% 7.36/1.50  --sat_fm_uc_incr                        true
% 7.36/1.50  --sat_out_model                         small
% 7.36/1.50  --sat_out_clauses                       false
% 7.36/1.50  
% 7.36/1.50  ------ QBF Options
% 7.36/1.50  
% 7.36/1.50  --qbf_mode                              false
% 7.36/1.50  --qbf_elim_univ                         false
% 7.36/1.50  --qbf_dom_inst                          none
% 7.36/1.50  --qbf_dom_pre_inst                      false
% 7.36/1.50  --qbf_sk_in                             false
% 7.36/1.50  --qbf_pred_elim                         true
% 7.36/1.50  --qbf_split                             512
% 7.36/1.50  
% 7.36/1.50  ------ BMC1 Options
% 7.36/1.50  
% 7.36/1.50  --bmc1_incremental                      false
% 7.36/1.50  --bmc1_axioms                           reachable_all
% 7.36/1.50  --bmc1_min_bound                        0
% 7.36/1.50  --bmc1_max_bound                        -1
% 7.36/1.50  --bmc1_max_bound_default                -1
% 7.36/1.50  --bmc1_symbol_reachability              true
% 7.36/1.50  --bmc1_property_lemmas                  false
% 7.36/1.50  --bmc1_k_induction                      false
% 7.36/1.50  --bmc1_non_equiv_states                 false
% 7.36/1.50  --bmc1_deadlock                         false
% 7.36/1.50  --bmc1_ucm                              false
% 7.36/1.50  --bmc1_add_unsat_core                   none
% 7.36/1.50  --bmc1_unsat_core_children              false
% 7.36/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.50  --bmc1_out_stat                         full
% 7.36/1.50  --bmc1_ground_init                      false
% 7.36/1.50  --bmc1_pre_inst_next_state              false
% 7.36/1.50  --bmc1_pre_inst_state                   false
% 7.36/1.50  --bmc1_pre_inst_reach_state             false
% 7.36/1.50  --bmc1_out_unsat_core                   false
% 7.36/1.50  --bmc1_aig_witness_out                  false
% 7.36/1.50  --bmc1_verbose                          false
% 7.36/1.50  --bmc1_dump_clauses_tptp                false
% 7.36/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.50  --bmc1_dump_file                        -
% 7.36/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.50  --bmc1_ucm_extend_mode                  1
% 7.36/1.50  --bmc1_ucm_init_mode                    2
% 7.36/1.50  --bmc1_ucm_cone_mode                    none
% 7.36/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.50  --bmc1_ucm_relax_model                  4
% 7.36/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.50  --bmc1_ucm_layered_model                none
% 7.36/1.50  --bmc1_ucm_max_lemma_size               10
% 7.36/1.50  
% 7.36/1.50  ------ AIG Options
% 7.36/1.50  
% 7.36/1.50  --aig_mode                              false
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation Options
% 7.36/1.50  
% 7.36/1.50  --instantiation_flag                    true
% 7.36/1.50  --inst_sos_flag                         true
% 7.36/1.50  --inst_sos_phase                        true
% 7.36/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel_side                     num_symb
% 7.36/1.50  --inst_solver_per_active                1400
% 7.36/1.50  --inst_solver_calls_frac                1.
% 7.36/1.50  --inst_passive_queue_type               priority_queues
% 7.36/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.50  --inst_passive_queues_freq              [25;2]
% 7.36/1.50  --inst_dismatching                      true
% 7.36/1.50  --inst_eager_unprocessed_to_passive     true
% 7.36/1.50  --inst_prop_sim_given                   true
% 7.36/1.50  --inst_prop_sim_new                     false
% 7.36/1.50  --inst_subs_new                         false
% 7.36/1.50  --inst_eq_res_simp                      false
% 7.36/1.50  --inst_subs_given                       false
% 7.36/1.50  --inst_orphan_elimination               true
% 7.36/1.50  --inst_learning_loop_flag               true
% 7.36/1.50  --inst_learning_start                   3000
% 7.36/1.50  --inst_learning_factor                  2
% 7.36/1.50  --inst_start_prop_sim_after_learn       3
% 7.36/1.50  --inst_sel_renew                        solver
% 7.36/1.50  --inst_lit_activity_flag                true
% 7.36/1.50  --inst_restr_to_given                   false
% 7.36/1.50  --inst_activity_threshold               500
% 7.36/1.50  --inst_out_proof                        true
% 7.36/1.50  
% 7.36/1.50  ------ Resolution Options
% 7.36/1.50  
% 7.36/1.50  --resolution_flag                       true
% 7.36/1.50  --res_lit_sel                           adaptive
% 7.36/1.50  --res_lit_sel_side                      none
% 7.36/1.50  --res_ordering                          kbo
% 7.36/1.50  --res_to_prop_solver                    active
% 7.36/1.50  --res_prop_simpl_new                    false
% 7.36/1.50  --res_prop_simpl_given                  true
% 7.36/1.50  --res_passive_queue_type                priority_queues
% 7.36/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.50  --res_passive_queues_freq               [15;5]
% 7.36/1.50  --res_forward_subs                      full
% 7.36/1.50  --res_backward_subs                     full
% 7.36/1.50  --res_forward_subs_resolution           true
% 7.36/1.50  --res_backward_subs_resolution          true
% 7.36/1.50  --res_orphan_elimination                true
% 7.36/1.50  --res_time_limit                        2.
% 7.36/1.50  --res_out_proof                         true
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Options
% 7.36/1.50  
% 7.36/1.50  --superposition_flag                    true
% 7.36/1.50  --sup_passive_queue_type                priority_queues
% 7.36/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.50  --demod_completeness_check              fast
% 7.36/1.50  --demod_use_ground                      true
% 7.36/1.50  --sup_to_prop_solver                    passive
% 7.36/1.50  --sup_prop_simpl_new                    true
% 7.36/1.50  --sup_prop_simpl_given                  true
% 7.36/1.50  --sup_fun_splitting                     true
% 7.36/1.50  --sup_smt_interval                      50000
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Simplification Setup
% 7.36/1.50  
% 7.36/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.50  --sup_immed_triv                        [TrivRules]
% 7.36/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_immed_bw_main                     []
% 7.36/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_input_bw                          []
% 7.36/1.50  
% 7.36/1.50  ------ Combination Options
% 7.36/1.50  
% 7.36/1.50  --comb_res_mult                         3
% 7.36/1.50  --comb_sup_mult                         2
% 7.36/1.50  --comb_inst_mult                        10
% 7.36/1.50  
% 7.36/1.50  ------ Debug Options
% 7.36/1.50  
% 7.36/1.50  --dbg_backtrace                         false
% 7.36/1.50  --dbg_dump_prop_clauses                 false
% 7.36/1.50  --dbg_dump_prop_clauses_file            -
% 7.36/1.50  --dbg_out_stat                          false
% 7.36/1.50  ------ Parsing...
% 7.36/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.36/1.50  ------ Proving...
% 7.36/1.50  ------ Problem Properties 
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  clauses                                 23
% 7.36/1.50  conjectures                             1
% 7.36/1.50  EPR                                     0
% 7.36/1.50  Horn                                    16
% 7.36/1.50  unary                                   8
% 7.36/1.50  binary                                  7
% 7.36/1.50  lits                                    48
% 7.36/1.50  lits eq                                 15
% 7.36/1.50  fd_pure                                 0
% 7.36/1.50  fd_pseudo                               0
% 7.36/1.50  fd_cond                                 0
% 7.36/1.50  fd_pseudo_cond                          6
% 7.36/1.50  AC symbols                              0
% 7.36/1.50  
% 7.36/1.50  ------ Schedule dynamic 5 is on 
% 7.36/1.50  
% 7.36/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  ------ 
% 7.36/1.50  Current options:
% 7.36/1.50  ------ 
% 7.36/1.50  
% 7.36/1.50  ------ Input Options
% 7.36/1.50  
% 7.36/1.50  --out_options                           all
% 7.36/1.50  --tptp_safe_out                         true
% 7.36/1.50  --problem_path                          ""
% 7.36/1.50  --include_path                          ""
% 7.36/1.50  --clausifier                            res/vclausify_rel
% 7.36/1.50  --clausifier_options                    ""
% 7.36/1.50  --stdin                                 false
% 7.36/1.50  --stats_out                             all
% 7.36/1.50  
% 7.36/1.50  ------ General Options
% 7.36/1.50  
% 7.36/1.50  --fof                                   false
% 7.36/1.50  --time_out_real                         305.
% 7.36/1.50  --time_out_virtual                      -1.
% 7.36/1.50  --symbol_type_check                     false
% 7.36/1.50  --clausify_out                          false
% 7.36/1.50  --sig_cnt_out                           false
% 7.36/1.50  --trig_cnt_out                          false
% 7.36/1.50  --trig_cnt_out_tolerance                1.
% 7.36/1.50  --trig_cnt_out_sk_spl                   false
% 7.36/1.50  --abstr_cl_out                          false
% 7.36/1.50  
% 7.36/1.50  ------ Global Options
% 7.36/1.50  
% 7.36/1.50  --schedule                              default
% 7.36/1.50  --add_important_lit                     false
% 7.36/1.50  --prop_solver_per_cl                    1000
% 7.36/1.50  --min_unsat_core                        false
% 7.36/1.50  --soft_assumptions                      false
% 7.36/1.50  --soft_lemma_size                       3
% 7.36/1.50  --prop_impl_unit_size                   0
% 7.36/1.50  --prop_impl_unit                        []
% 7.36/1.50  --share_sel_clauses                     true
% 7.36/1.50  --reset_solvers                         false
% 7.36/1.50  --bc_imp_inh                            [conj_cone]
% 7.36/1.50  --conj_cone_tolerance                   3.
% 7.36/1.50  --extra_neg_conj                        none
% 7.36/1.50  --large_theory_mode                     true
% 7.36/1.50  --prolific_symb_bound                   200
% 7.36/1.50  --lt_threshold                          2000
% 7.36/1.50  --clause_weak_htbl                      true
% 7.36/1.50  --gc_record_bc_elim                     false
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing Options
% 7.36/1.50  
% 7.36/1.50  --preprocessing_flag                    true
% 7.36/1.50  --time_out_prep_mult                    0.1
% 7.36/1.50  --splitting_mode                        input
% 7.36/1.50  --splitting_grd                         true
% 7.36/1.50  --splitting_cvd                         false
% 7.36/1.50  --splitting_cvd_svl                     false
% 7.36/1.50  --splitting_nvd                         32
% 7.36/1.50  --sub_typing                            true
% 7.36/1.50  --prep_gs_sim                           true
% 7.36/1.50  --prep_unflatten                        true
% 7.36/1.50  --prep_res_sim                          true
% 7.36/1.50  --prep_upred                            true
% 7.36/1.50  --prep_sem_filter                       exhaustive
% 7.36/1.50  --prep_sem_filter_out                   false
% 7.36/1.50  --pred_elim                             true
% 7.36/1.50  --res_sim_input                         true
% 7.36/1.50  --eq_ax_congr_red                       true
% 7.36/1.50  --pure_diseq_elim                       true
% 7.36/1.50  --brand_transform                       false
% 7.36/1.50  --non_eq_to_eq                          false
% 7.36/1.50  --prep_def_merge                        true
% 7.36/1.50  --prep_def_merge_prop_impl              false
% 7.36/1.50  --prep_def_merge_mbd                    true
% 7.36/1.50  --prep_def_merge_tr_red                 false
% 7.36/1.50  --prep_def_merge_tr_cl                  false
% 7.36/1.50  --smt_preprocessing                     true
% 7.36/1.50  --smt_ac_axioms                         fast
% 7.36/1.50  --preprocessed_out                      false
% 7.36/1.50  --preprocessed_stats                    false
% 7.36/1.50  
% 7.36/1.50  ------ Abstraction refinement Options
% 7.36/1.50  
% 7.36/1.50  --abstr_ref                             []
% 7.36/1.50  --abstr_ref_prep                        false
% 7.36/1.50  --abstr_ref_until_sat                   false
% 7.36/1.50  --abstr_ref_sig_restrict                funpre
% 7.36/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.50  --abstr_ref_under                       []
% 7.36/1.50  
% 7.36/1.50  ------ SAT Options
% 7.36/1.50  
% 7.36/1.50  --sat_mode                              false
% 7.36/1.50  --sat_fm_restart_options                ""
% 7.36/1.50  --sat_gr_def                            false
% 7.36/1.50  --sat_epr_types                         true
% 7.36/1.50  --sat_non_cyclic_types                  false
% 7.36/1.50  --sat_finite_models                     false
% 7.36/1.50  --sat_fm_lemmas                         false
% 7.36/1.50  --sat_fm_prep                           false
% 7.36/1.50  --sat_fm_uc_incr                        true
% 7.36/1.50  --sat_out_model                         small
% 7.36/1.50  --sat_out_clauses                       false
% 7.36/1.50  
% 7.36/1.50  ------ QBF Options
% 7.36/1.50  
% 7.36/1.50  --qbf_mode                              false
% 7.36/1.50  --qbf_elim_univ                         false
% 7.36/1.50  --qbf_dom_inst                          none
% 7.36/1.50  --qbf_dom_pre_inst                      false
% 7.36/1.50  --qbf_sk_in                             false
% 7.36/1.50  --qbf_pred_elim                         true
% 7.36/1.50  --qbf_split                             512
% 7.36/1.50  
% 7.36/1.50  ------ BMC1 Options
% 7.36/1.50  
% 7.36/1.50  --bmc1_incremental                      false
% 7.36/1.50  --bmc1_axioms                           reachable_all
% 7.36/1.50  --bmc1_min_bound                        0
% 7.36/1.50  --bmc1_max_bound                        -1
% 7.36/1.50  --bmc1_max_bound_default                -1
% 7.36/1.50  --bmc1_symbol_reachability              true
% 7.36/1.50  --bmc1_property_lemmas                  false
% 7.36/1.50  --bmc1_k_induction                      false
% 7.36/1.50  --bmc1_non_equiv_states                 false
% 7.36/1.50  --bmc1_deadlock                         false
% 7.36/1.50  --bmc1_ucm                              false
% 7.36/1.50  --bmc1_add_unsat_core                   none
% 7.36/1.50  --bmc1_unsat_core_children              false
% 7.36/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.50  --bmc1_out_stat                         full
% 7.36/1.50  --bmc1_ground_init                      false
% 7.36/1.50  --bmc1_pre_inst_next_state              false
% 7.36/1.50  --bmc1_pre_inst_state                   false
% 7.36/1.50  --bmc1_pre_inst_reach_state             false
% 7.36/1.50  --bmc1_out_unsat_core                   false
% 7.36/1.50  --bmc1_aig_witness_out                  false
% 7.36/1.50  --bmc1_verbose                          false
% 7.36/1.50  --bmc1_dump_clauses_tptp                false
% 7.36/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.50  --bmc1_dump_file                        -
% 7.36/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.50  --bmc1_ucm_extend_mode                  1
% 7.36/1.50  --bmc1_ucm_init_mode                    2
% 7.36/1.50  --bmc1_ucm_cone_mode                    none
% 7.36/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.50  --bmc1_ucm_relax_model                  4
% 7.36/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.50  --bmc1_ucm_layered_model                none
% 7.36/1.50  --bmc1_ucm_max_lemma_size               10
% 7.36/1.50  
% 7.36/1.50  ------ AIG Options
% 7.36/1.50  
% 7.36/1.50  --aig_mode                              false
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation Options
% 7.36/1.50  
% 7.36/1.50  --instantiation_flag                    true
% 7.36/1.50  --inst_sos_flag                         true
% 7.36/1.50  --inst_sos_phase                        true
% 7.36/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel_side                     none
% 7.36/1.50  --inst_solver_per_active                1400
% 7.36/1.50  --inst_solver_calls_frac                1.
% 7.36/1.50  --inst_passive_queue_type               priority_queues
% 7.36/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.50  --inst_passive_queues_freq              [25;2]
% 7.36/1.50  --inst_dismatching                      true
% 7.36/1.50  --inst_eager_unprocessed_to_passive     true
% 7.36/1.50  --inst_prop_sim_given                   true
% 7.36/1.50  --inst_prop_sim_new                     false
% 7.36/1.50  --inst_subs_new                         false
% 7.36/1.50  --inst_eq_res_simp                      false
% 7.36/1.50  --inst_subs_given                       false
% 7.36/1.50  --inst_orphan_elimination               true
% 7.36/1.50  --inst_learning_loop_flag               true
% 7.36/1.50  --inst_learning_start                   3000
% 7.36/1.50  --inst_learning_factor                  2
% 7.36/1.50  --inst_start_prop_sim_after_learn       3
% 7.36/1.50  --inst_sel_renew                        solver
% 7.36/1.50  --inst_lit_activity_flag                true
% 7.36/1.50  --inst_restr_to_given                   false
% 7.36/1.50  --inst_activity_threshold               500
% 7.36/1.50  --inst_out_proof                        true
% 7.36/1.50  
% 7.36/1.50  ------ Resolution Options
% 7.36/1.50  
% 7.36/1.50  --resolution_flag                       false
% 7.36/1.50  --res_lit_sel                           adaptive
% 7.36/1.50  --res_lit_sel_side                      none
% 7.36/1.50  --res_ordering                          kbo
% 7.36/1.50  --res_to_prop_solver                    active
% 7.36/1.50  --res_prop_simpl_new                    false
% 7.36/1.50  --res_prop_simpl_given                  true
% 7.36/1.50  --res_passive_queue_type                priority_queues
% 7.36/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.50  --res_passive_queues_freq               [15;5]
% 7.36/1.50  --res_forward_subs                      full
% 7.36/1.50  --res_backward_subs                     full
% 7.36/1.50  --res_forward_subs_resolution           true
% 7.36/1.50  --res_backward_subs_resolution          true
% 7.36/1.50  --res_orphan_elimination                true
% 7.36/1.50  --res_time_limit                        2.
% 7.36/1.50  --res_out_proof                         true
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Options
% 7.36/1.50  
% 7.36/1.50  --superposition_flag                    true
% 7.36/1.50  --sup_passive_queue_type                priority_queues
% 7.36/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.50  --demod_completeness_check              fast
% 7.36/1.50  --demod_use_ground                      true
% 7.36/1.50  --sup_to_prop_solver                    passive
% 7.36/1.50  --sup_prop_simpl_new                    true
% 7.36/1.50  --sup_prop_simpl_given                  true
% 7.36/1.50  --sup_fun_splitting                     true
% 7.36/1.50  --sup_smt_interval                      50000
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Simplification Setup
% 7.36/1.50  
% 7.36/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.50  --sup_immed_triv                        [TrivRules]
% 7.36/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_immed_bw_main                     []
% 7.36/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_input_bw                          []
% 7.36/1.50  
% 7.36/1.50  ------ Combination Options
% 7.36/1.50  
% 7.36/1.50  --comb_res_mult                         3
% 7.36/1.50  --comb_sup_mult                         2
% 7.36/1.50  --comb_inst_mult                        10
% 7.36/1.50  
% 7.36/1.50  ------ Debug Options
% 7.36/1.50  
% 7.36/1.50  --dbg_backtrace                         false
% 7.36/1.50  --dbg_dump_prop_clauses                 false
% 7.36/1.50  --dbg_dump_prop_clauses_file            -
% 7.36/1.50  --dbg_out_stat                          false
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  ------ Proving...
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  % SZS status Theorem for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50   Resolution empty clause
% 7.36/1.50  
% 7.36/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  fof(f5,axiom,(
% 7.36/1.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f18,plain,(
% 7.36/1.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.36/1.50    inference(rectify,[],[f5])).
% 7.36/1.50  
% 7.36/1.50  fof(f52,plain,(
% 7.36/1.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.36/1.50    inference(cnf_transformation,[],[f18])).
% 7.36/1.50  
% 7.36/1.50  fof(f12,axiom,(
% 7.36/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f59,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.36/1.50    inference(cnf_transformation,[],[f12])).
% 7.36/1.50  
% 7.36/1.50  fof(f6,axiom,(
% 7.36/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f53,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.36/1.50    inference(cnf_transformation,[],[f6])).
% 7.36/1.50  
% 7.36/1.50  fof(f64,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.36/1.50    inference(definition_unfolding,[],[f59,f53])).
% 7.36/1.50  
% 7.36/1.50  fof(f74,plain,(
% 7.36/1.50    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 7.36/1.50    inference(definition_unfolding,[],[f52,f64])).
% 7.36/1.50  
% 7.36/1.50  fof(f10,axiom,(
% 7.36/1.50    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f57,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.36/1.50    inference(cnf_transformation,[],[f10])).
% 7.36/1.50  
% 7.36/1.50  fof(f78,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 7.36/1.50    inference(definition_unfolding,[],[f57,f53,f64])).
% 7.36/1.50  
% 7.36/1.50  fof(f2,axiom,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f19,plain,(
% 7.36/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.36/1.50    inference(unused_predicate_definition_removal,[],[f2])).
% 7.36/1.50  
% 7.36/1.50  fof(f20,plain,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.36/1.50    inference(ennf_transformation,[],[f19])).
% 7.36/1.50  
% 7.36/1.50  fof(f23,plain,(
% 7.36/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f24,plain,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).
% 7.36/1.50  
% 7.36/1.50  fof(f38,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f24])).
% 7.36/1.50  
% 7.36/1.50  fof(f1,axiom,(
% 7.36/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f37,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f1])).
% 7.36/1.50  
% 7.36/1.50  fof(f9,axiom,(
% 7.36/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f56,plain,(
% 7.36/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.36/1.50    inference(cnf_transformation,[],[f9])).
% 7.36/1.50  
% 7.36/1.50  fof(f77,plain,(
% 7.36/1.50    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 7.36/1.50    inference(definition_unfolding,[],[f56,f53])).
% 7.36/1.50  
% 7.36/1.50  fof(f4,axiom,(
% 7.36/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f30,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(nnf_transformation,[],[f4])).
% 7.36/1.50  
% 7.36/1.50  fof(f31,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(flattening,[],[f30])).
% 7.36/1.50  
% 7.36/1.50  fof(f32,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(rectify,[],[f31])).
% 7.36/1.50  
% 7.36/1.50  fof(f33,plain,(
% 7.36/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f34,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 7.36/1.50  
% 7.36/1.50  fof(f47,plain,(
% 7.36/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.36/1.50    inference(cnf_transformation,[],[f34])).
% 7.36/1.50  
% 7.36/1.50  fof(f72,plain,(
% 7.36/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.36/1.50    inference(definition_unfolding,[],[f47,f53])).
% 7.36/1.50  
% 7.36/1.50  fof(f84,plain,(
% 7.36/1.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.36/1.50    inference(equality_resolution,[],[f72])).
% 7.36/1.50  
% 7.36/1.50  fof(f7,axiom,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f21,plain,(
% 7.36/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.36/1.50    inference(ennf_transformation,[],[f7])).
% 7.36/1.50  
% 7.36/1.50  fof(f54,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f21])).
% 7.36/1.50  
% 7.36/1.50  fof(f75,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 7.36/1.50    inference(definition_unfolding,[],[f54,f64])).
% 7.36/1.50  
% 7.36/1.50  fof(f11,axiom,(
% 7.36/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f58,plain,(
% 7.36/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f11])).
% 7.36/1.50  
% 7.36/1.50  fof(f3,axiom,(
% 7.36/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f25,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(nnf_transformation,[],[f3])).
% 7.36/1.50  
% 7.36/1.50  fof(f26,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(flattening,[],[f25])).
% 7.36/1.50  
% 7.36/1.50  fof(f27,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(rectify,[],[f26])).
% 7.36/1.50  
% 7.36/1.50  fof(f28,plain,(
% 7.36/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f29,plain,(
% 7.36/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.36/1.50  
% 7.36/1.50  fof(f40,plain,(
% 7.36/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.36/1.50    inference(cnf_transformation,[],[f29])).
% 7.36/1.50  
% 7.36/1.50  fof(f82,plain,(
% 7.36/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.36/1.50    inference(equality_resolution,[],[f40])).
% 7.36/1.50  
% 7.36/1.50  fof(f39,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f24])).
% 7.36/1.50  
% 7.36/1.50  fof(f16,conjecture,(
% 7.36/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f17,negated_conjecture,(
% 7.36/1.50    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.36/1.50    inference(negated_conjecture,[],[f16])).
% 7.36/1.50  
% 7.36/1.50  fof(f22,plain,(
% 7.36/1.50    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 7.36/1.50    inference(ennf_transformation,[],[f17])).
% 7.36/1.50  
% 7.36/1.50  fof(f35,plain,(
% 7.36/1.50    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f36,plain,(
% 7.36/1.50    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f35])).
% 7.36/1.50  
% 7.36/1.50  fof(f63,plain,(
% 7.36/1.50    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 7.36/1.50    inference(cnf_transformation,[],[f36])).
% 7.36/1.50  
% 7.36/1.50  fof(f14,axiom,(
% 7.36/1.50    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f61,plain,(
% 7.36/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f14])).
% 7.36/1.50  
% 7.36/1.50  fof(f13,axiom,(
% 7.36/1.50    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f60,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f13])).
% 7.36/1.50  
% 7.36/1.50  fof(f65,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 7.36/1.50    inference(definition_unfolding,[],[f60,f64])).
% 7.36/1.50  
% 7.36/1.50  fof(f66,plain,(
% 7.36/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2)) )),
% 7.36/1.50    inference(definition_unfolding,[],[f61,f64,f65])).
% 7.36/1.50  
% 7.36/1.50  fof(f79,plain,(
% 7.36/1.50    k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK3))))),
% 7.36/1.50    inference(definition_unfolding,[],[f63,f65,f66])).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 7.36/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_20,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.36/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1100,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16,c_20]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3,plain,
% 7.36/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.36/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_452,plain,
% 7.36/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.36/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1,plain,
% 7.36/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.36/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.36/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_795,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1,c_19]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14,plain,
% 7.36/1.50      ( ~ r2_hidden(X0,X1)
% 7.36/1.50      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.36/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_441,plain,
% 7.36/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.50      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2847,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_795,c_441]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4466,plain,
% 7.36/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_452,c_2847]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17,plain,
% 7.36/1.50      ( ~ r1_tarski(X0,X1)
% 7.36/1.50      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 7.36/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_439,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
% 7.36/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4567,plain,
% 7.36/1.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_4466,c_439]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4568,plain,
% 7.36/1.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_4567,c_19]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_21,plain,
% 7.36/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.36/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1293,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1100,c_21]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4572,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = X1 ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_4568,c_1293]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5295,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1100,c_4572]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1288,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_1100,c_16]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5309,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_5295,c_1288]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5301,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X0),X0))) = k1_xboole_0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_4572,c_20]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5463,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)),k3_xboole_0(X0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5301,c_4572]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5464,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_5463,c_1288,c_5309]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9,plain,
% 7.36/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 7.36/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_446,plain,
% 7.36/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.36/1.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6177,plain,
% 7.36/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.50      | r2_hidden(X0,k3_xboole_0(X1,X1)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5464,c_446]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2,plain,
% 7.36/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.36/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_453,plain,
% 7.36/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.36/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_8705,plain,
% 7.36/1.50      ( r2_hidden(sK0(X0,k3_xboole_0(X1,X1)),X1) != iProver_top
% 7.36/1.50      | r1_tarski(X0,k3_xboole_0(X1,X1)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_6177,c_453]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17871,plain,
% 7.36/1.50      ( r1_tarski(X0,k3_xboole_0(X0,X0)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_452,c_8705]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17918,plain,
% 7.36/1.50      ( r1_tarski(k3_xboole_0(X0,X0),X0) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5309,c_17871]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_18026,plain,
% 7.36/1.50      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0)))) = X0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_17918,c_439]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5324,plain,
% 7.36/1.50      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5309,c_4572]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5720,plain,
% 7.36/1.50      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_20,c_5324]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5735,plain,
% 7.36/1.50      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X0) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_5720,c_1288]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19304,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k3_xboole_0(k3_xboole_0(X0,X0),X0) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_18026,c_5735]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1294,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1100,c_21]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5907,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1294,c_5324]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5920,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,X0))) = k3_xboole_0(X1,X1) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_5907,c_1288]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7775,plain,
% 7.36/1.50      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X1)),k5_xboole_0(X0,k3_xboole_0(X1,X1))) = k5_xboole_0(X1,k3_xboole_0(X0,X0)) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5920,c_4572]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5721,plain,
% 7.36/1.50      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_21,c_5324]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_12006,plain,
% 7.36/1.50      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X1)),k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X0),X2))) = X2 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_7775,c_5721]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19369,plain,
% 7.36/1.50      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)),k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)))),k3_xboole_0(X0,X0)) = k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_18026,c_12006]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19385,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19369,c_1100,c_5309]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19386,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = k3_xboole_0(X0,X0) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_19385,c_4568]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19462,plain,
% 7.36/1.50      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_19304,c_19386]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19463,plain,
% 7.36/1.50      ( k3_xboole_0(X0,X0) = X0 ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19462,c_5309]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1107,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1,c_20]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5865,plain,
% 7.36/1.50      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1107,c_5324]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5873,plain,
% 7.36/1.50      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X0) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_5865,c_1288]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_22,negated_conjecture,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK3)))) ),
% 7.36/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_537,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k1_tarski(sK3)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_1,c_22]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_672,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1,c_537]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1074,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_21,c_672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1430,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_21,c_1074]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6876,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK3)))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_5873,c_1430]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19817,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK3))))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_19463,c_6876]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7759,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_21,c_5920]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19838,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,X2) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_19463,c_7759]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19841,plain,
% 7.36/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_19838,c_19463]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19850,plain,
% 7.36/1.50      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) != k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_19817,c_19841]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19851,plain,
% 7.36/1.50      ( $false ),
% 7.36/1.50      inference(equality_resolution_simp,[status(thm)],[c_19850]) ).
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  ------                               Statistics
% 7.36/1.50  
% 7.36/1.50  ------ General
% 7.36/1.50  
% 7.36/1.50  abstr_ref_over_cycles:                  0
% 7.36/1.50  abstr_ref_under_cycles:                 0
% 7.36/1.50  gc_basic_clause_elim:                   0
% 7.36/1.50  forced_gc_time:                         0
% 7.36/1.50  parsing_time:                           0.013
% 7.36/1.50  unif_index_cands_time:                  0.
% 7.36/1.50  unif_index_add_time:                    0.
% 7.36/1.50  orderings_time:                         0.
% 7.36/1.50  out_proof_time:                         0.01
% 7.36/1.50  total_time:                             0.684
% 7.36/1.50  num_of_symbols:                         42
% 7.36/1.50  num_of_terms:                           30770
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing
% 7.36/1.50  
% 7.36/1.50  num_of_splits:                          0
% 7.36/1.50  num_of_split_atoms:                     0
% 7.36/1.50  num_of_reused_defs:                     0
% 7.36/1.50  num_eq_ax_congr_red:                    20
% 7.36/1.50  num_of_sem_filtered_clauses:            1
% 7.36/1.50  num_of_subtypes:                        0
% 7.36/1.50  monotx_restored_types:                  0
% 7.36/1.50  sat_num_of_epr_types:                   0
% 7.36/1.50  sat_num_of_non_cyclic_types:            0
% 7.36/1.50  sat_guarded_non_collapsed_types:        0
% 7.36/1.50  num_pure_diseq_elim:                    0
% 7.36/1.50  simp_replaced_by:                       0
% 7.36/1.50  res_preprocessed:                       82
% 7.36/1.50  prep_upred:                             0
% 7.36/1.50  prep_unflattend:                        0
% 7.36/1.50  smt_new_axioms:                         0
% 7.36/1.50  pred_elim_cands:                        2
% 7.36/1.50  pred_elim:                              0
% 7.36/1.50  pred_elim_cl:                           0
% 7.36/1.50  pred_elim_cycles:                       1
% 7.36/1.50  merged_defs:                            0
% 7.36/1.50  merged_defs_ncl:                        0
% 7.36/1.50  bin_hyper_res:                          0
% 7.36/1.50  prep_cycles:                            3
% 7.36/1.50  pred_elim_time:                         0.
% 7.36/1.50  splitting_time:                         0.
% 7.36/1.50  sem_filter_time:                        0.
% 7.36/1.50  monotx_time:                            0.001
% 7.36/1.50  subtype_inf_time:                       0.
% 7.36/1.50  
% 7.36/1.50  ------ Problem properties
% 7.36/1.50  
% 7.36/1.50  clauses:                                23
% 7.36/1.50  conjectures:                            1
% 7.36/1.50  epr:                                    0
% 7.36/1.50  horn:                                   16
% 7.36/1.50  ground:                                 1
% 7.36/1.50  unary:                                  8
% 7.36/1.50  binary:                                 7
% 7.36/1.50  lits:                                   48
% 7.36/1.50  lits_eq:                                15
% 7.36/1.50  fd_pure:                                0
% 7.36/1.50  fd_pseudo:                              0
% 7.36/1.50  fd_cond:                                0
% 7.36/1.50  fd_pseudo_cond:                         6
% 7.36/1.50  ac_symbols:                             0
% 7.36/1.50  
% 7.36/1.50  ------ Propositional Solver
% 7.36/1.50  
% 7.36/1.50  prop_solver_calls:                      26
% 7.36/1.50  prop_fast_solver_calls:                 660
% 7.36/1.50  smt_solver_calls:                       0
% 7.36/1.50  smt_fast_solver_calls:                  0
% 7.36/1.50  prop_num_of_clauses:                    6946
% 7.36/1.50  prop_preprocess_simplified:             12528
% 7.36/1.50  prop_fo_subsumed:                       1
% 7.36/1.50  prop_solver_time:                       0.
% 7.36/1.50  smt_solver_time:                        0.
% 7.36/1.50  smt_fast_solver_time:                   0.
% 7.36/1.50  prop_fast_solver_time:                  0.
% 7.36/1.50  prop_unsat_core_time:                   0.
% 7.36/1.50  
% 7.36/1.50  ------ QBF
% 7.36/1.50  
% 7.36/1.50  qbf_q_res:                              0
% 7.36/1.50  qbf_num_tautologies:                    0
% 7.36/1.50  qbf_prep_cycles:                        0
% 7.36/1.50  
% 7.36/1.50  ------ BMC1
% 7.36/1.50  
% 7.36/1.50  bmc1_current_bound:                     -1
% 7.36/1.50  bmc1_last_solved_bound:                 -1
% 7.36/1.50  bmc1_unsat_core_size:                   -1
% 7.36/1.50  bmc1_unsat_core_parents_size:           -1
% 7.36/1.50  bmc1_merge_next_fun:                    0
% 7.36/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation
% 7.36/1.50  
% 7.36/1.50  inst_num_of_clauses:                    1680
% 7.36/1.50  inst_num_in_passive:                    780
% 7.36/1.50  inst_num_in_active:                     593
% 7.36/1.50  inst_num_in_unprocessed:                307
% 7.36/1.50  inst_num_of_loops:                      730
% 7.36/1.50  inst_num_of_learning_restarts:          0
% 7.36/1.50  inst_num_moves_active_passive:          136
% 7.36/1.50  inst_lit_activity:                      0
% 7.36/1.50  inst_lit_activity_moves:                0
% 7.36/1.50  inst_num_tautologies:                   0
% 7.36/1.50  inst_num_prop_implied:                  0
% 7.36/1.50  inst_num_existing_simplified:           0
% 7.36/1.50  inst_num_eq_res_simplified:             0
% 7.36/1.50  inst_num_child_elim:                    0
% 7.36/1.50  inst_num_of_dismatching_blockings:      1234
% 7.36/1.50  inst_num_of_non_proper_insts:           1900
% 7.36/1.50  inst_num_of_duplicates:                 0
% 7.36/1.50  inst_inst_num_from_inst_to_res:         0
% 7.36/1.50  inst_dismatching_checking_time:         0.
% 7.36/1.50  
% 7.36/1.50  ------ Resolution
% 7.36/1.50  
% 7.36/1.50  res_num_of_clauses:                     0
% 7.36/1.50  res_num_in_passive:                     0
% 7.36/1.50  res_num_in_active:                      0
% 7.36/1.50  res_num_of_loops:                       85
% 7.36/1.50  res_forward_subset_subsumed:            126
% 7.36/1.50  res_backward_subset_subsumed:           0
% 7.36/1.50  res_forward_subsumed:                   0
% 7.36/1.50  res_backward_subsumed:                  0
% 7.36/1.50  res_forward_subsumption_resolution:     0
% 7.36/1.50  res_backward_subsumption_resolution:    0
% 7.36/1.50  res_clause_to_clause_subsumption:       5420
% 7.36/1.50  res_orphan_elimination:                 0
% 7.36/1.50  res_tautology_del:                      104
% 7.36/1.50  res_num_eq_res_simplified:              0
% 7.36/1.50  res_num_sel_changes:                    0
% 7.36/1.50  res_moves_from_active_to_pass:          0
% 7.36/1.50  
% 7.36/1.50  ------ Superposition
% 7.36/1.50  
% 7.36/1.50  sup_time_total:                         0.
% 7.36/1.50  sup_time_generating:                    0.
% 7.36/1.50  sup_time_sim_full:                      0.
% 7.36/1.50  sup_time_sim_immed:                     0.
% 7.36/1.50  
% 7.36/1.50  sup_num_of_clauses:                     618
% 7.36/1.50  sup_num_in_active:                      31
% 7.36/1.50  sup_num_in_passive:                     587
% 7.36/1.50  sup_num_of_loops:                       144
% 7.36/1.50  sup_fw_superposition:                   2602
% 7.36/1.50  sup_bw_superposition:                   1754
% 7.36/1.50  sup_immediate_simplified:               2239
% 7.36/1.50  sup_given_eliminated:                   9
% 7.36/1.50  comparisons_done:                       0
% 7.36/1.50  comparisons_avoided:                    0
% 7.36/1.50  
% 7.36/1.50  ------ Simplifications
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  sim_fw_subset_subsumed:                 17
% 7.36/1.50  sim_bw_subset_subsumed:                 4
% 7.36/1.50  sim_fw_subsumed:                        226
% 7.36/1.50  sim_bw_subsumed:                        12
% 7.36/1.50  sim_fw_subsumption_res:                 0
% 7.36/1.50  sim_bw_subsumption_res:                 0
% 7.36/1.50  sim_tautology_del:                      65
% 7.36/1.50  sim_eq_tautology_del:                   1100
% 7.36/1.50  sim_eq_res_simp:                        3
% 7.36/1.50  sim_fw_demodulated:                     1950
% 7.36/1.50  sim_bw_demodulated:                     124
% 7.36/1.50  sim_light_normalised:                   937
% 7.36/1.50  sim_joinable_taut:                      0
% 7.36/1.50  sim_joinable_simp:                      0
% 7.36/1.50  sim_ac_normalised:                      0
% 7.36/1.50  sim_smt_subsumption:                    0
% 7.36/1.50  
%------------------------------------------------------------------------------
