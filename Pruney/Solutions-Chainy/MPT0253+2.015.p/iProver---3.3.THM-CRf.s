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
% DateTime   : Thu Dec  3 11:33:41 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 638 expanded)
%              Number of clauses        :   49 (  89 expanded)
%              Number of leaves         :   19 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          :  301 (1208 expanded)
%              Number of equality atoms :  118 ( 642 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k2_tarski(sK2,sK4),sK3) != sK3
      & r2_hidden(sK4,sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k2_xboole_0(k2_tarski(sK2,sK4),sK3) != sK3
    & r2_hidden(sK4,sK3)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f35])).

fof(f64,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f52,f69,f69,f49])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f68,f68])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f18])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f65,plain,(
    k2_xboole_0(k2_tarski(sK2,sK4),sK3) != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    k3_tarski(k4_enumset1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),sK3)) != sK3 ),
    inference(definition_unfolding,[],[f65,f69,f68])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_608,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_607,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_611,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_612,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2657,plain,
    ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) = k4_enumset1(X0,X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_612])).

cnf(c_3606,plain,
    ( k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,X0),sK3) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_2657])).

cnf(c_5013,plain,
    ( k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),sK3) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_608,c_3606])).

cnf(c_14,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5074,plain,
    ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4)))) = k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4))) ),
    inference(superposition,[status(thm)],[c_5013,c_14])).

cnf(c_12,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_618,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_613,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_609,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_993,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_609])).

cnf(c_1309,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_993])).

cnf(c_1001,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_16,c_12])).

cnf(c_1162,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1001,c_14])).

cnf(c_1163,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1162,c_1001])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_616,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1829,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_616])).

cnf(c_2329,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1829])).

cnf(c_2782,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_2329])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_622,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2340,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_2329])).

cnf(c_2423,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2340,c_612])).

cnf(c_2792,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2782,c_2423])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2793,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2792,c_15])).

cnf(c_910,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_613,c_612])).

cnf(c_1830,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_616])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_615,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1512,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_615])).

cnf(c_3261,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1830,c_1512])).

cnf(c_3271,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2793,c_3261])).

cnf(c_5076,plain,
    ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4))) = sK3 ),
    inference(demodulation,[status(thm)],[c_5074,c_12,c_3271])).

cnf(c_20,negated_conjecture,
    ( k3_tarski(k4_enumset1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_998,plain,
    ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4))) != sK3 ),
    inference(demodulation,[status(thm)],[c_16,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5076,c_998])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.92/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/0.97  
% 2.92/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.97  
% 2.92/0.97  ------  iProver source info
% 2.92/0.97  
% 2.92/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.97  git: non_committed_changes: false
% 2.92/0.97  git: last_make_outside_of_git: false
% 2.92/0.97  
% 2.92/0.97  ------ 
% 2.92/0.97  
% 2.92/0.97  ------ Input Options
% 2.92/0.97  
% 2.92/0.97  --out_options                           all
% 2.92/0.97  --tptp_safe_out                         true
% 2.92/0.97  --problem_path                          ""
% 2.92/0.97  --include_path                          ""
% 2.92/0.97  --clausifier                            res/vclausify_rel
% 2.92/0.97  --clausifier_options                    --mode clausify
% 2.92/0.97  --stdin                                 false
% 2.92/0.97  --stats_out                             all
% 2.92/0.97  
% 2.92/0.97  ------ General Options
% 2.92/0.97  
% 2.92/0.97  --fof                                   false
% 2.92/0.97  --time_out_real                         305.
% 2.92/0.97  --time_out_virtual                      -1.
% 2.92/0.97  --symbol_type_check                     false
% 2.92/0.97  --clausify_out                          false
% 2.92/0.97  --sig_cnt_out                           false
% 2.92/0.97  --trig_cnt_out                          false
% 2.92/0.97  --trig_cnt_out_tolerance                1.
% 2.92/0.97  --trig_cnt_out_sk_spl                   false
% 2.92/0.97  --abstr_cl_out                          false
% 2.92/0.97  
% 2.92/0.97  ------ Global Options
% 2.92/0.97  
% 2.92/0.97  --schedule                              default
% 2.92/0.97  --add_important_lit                     false
% 2.92/0.97  --prop_solver_per_cl                    1000
% 2.92/0.97  --min_unsat_core                        false
% 2.92/0.97  --soft_assumptions                      false
% 2.92/0.97  --soft_lemma_size                       3
% 2.92/0.97  --prop_impl_unit_size                   0
% 2.92/0.97  --prop_impl_unit                        []
% 2.92/0.97  --share_sel_clauses                     true
% 2.92/0.97  --reset_solvers                         false
% 2.92/0.97  --bc_imp_inh                            [conj_cone]
% 2.92/0.97  --conj_cone_tolerance                   3.
% 2.92/0.97  --extra_neg_conj                        none
% 2.92/0.97  --large_theory_mode                     true
% 2.92/0.97  --prolific_symb_bound                   200
% 2.92/0.97  --lt_threshold                          2000
% 2.92/0.97  --clause_weak_htbl                      true
% 2.92/0.97  --gc_record_bc_elim                     false
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing Options
% 2.92/0.97  
% 2.92/0.97  --preprocessing_flag                    true
% 2.92/0.97  --time_out_prep_mult                    0.1
% 2.92/0.97  --splitting_mode                        input
% 2.92/0.97  --splitting_grd                         true
% 2.92/0.97  --splitting_cvd                         false
% 2.92/0.97  --splitting_cvd_svl                     false
% 2.92/0.97  --splitting_nvd                         32
% 2.92/0.97  --sub_typing                            true
% 2.92/0.97  --prep_gs_sim                           true
% 2.92/0.97  --prep_unflatten                        true
% 2.92/0.97  --prep_res_sim                          true
% 2.92/0.97  --prep_upred                            true
% 2.92/0.97  --prep_sem_filter                       exhaustive
% 2.92/0.97  --prep_sem_filter_out                   false
% 2.92/0.97  --pred_elim                             true
% 2.92/0.97  --res_sim_input                         true
% 2.92/0.97  --eq_ax_congr_red                       true
% 2.92/0.97  --pure_diseq_elim                       true
% 2.92/0.97  --brand_transform                       false
% 2.92/0.97  --non_eq_to_eq                          false
% 2.92/0.97  --prep_def_merge                        true
% 2.92/0.97  --prep_def_merge_prop_impl              false
% 2.92/0.97  --prep_def_merge_mbd                    true
% 2.92/0.97  --prep_def_merge_tr_red                 false
% 2.92/0.97  --prep_def_merge_tr_cl                  false
% 2.92/0.97  --smt_preprocessing                     true
% 2.92/0.97  --smt_ac_axioms                         fast
% 2.92/0.97  --preprocessed_out                      false
% 2.92/0.97  --preprocessed_stats                    false
% 2.92/0.97  
% 2.92/0.97  ------ Abstraction refinement Options
% 2.92/0.97  
% 2.92/0.97  --abstr_ref                             []
% 2.92/0.97  --abstr_ref_prep                        false
% 2.92/0.97  --abstr_ref_until_sat                   false
% 2.92/0.97  --abstr_ref_sig_restrict                funpre
% 2.92/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.97  --abstr_ref_under                       []
% 2.92/0.97  
% 2.92/0.97  ------ SAT Options
% 2.92/0.97  
% 2.92/0.97  --sat_mode                              false
% 2.92/0.97  --sat_fm_restart_options                ""
% 2.92/0.97  --sat_gr_def                            false
% 2.92/0.97  --sat_epr_types                         true
% 2.92/0.97  --sat_non_cyclic_types                  false
% 2.92/0.97  --sat_finite_models                     false
% 2.92/0.97  --sat_fm_lemmas                         false
% 2.92/0.97  --sat_fm_prep                           false
% 2.92/0.97  --sat_fm_uc_incr                        true
% 2.92/0.97  --sat_out_model                         small
% 2.92/0.97  --sat_out_clauses                       false
% 2.92/0.97  
% 2.92/0.97  ------ QBF Options
% 2.92/0.97  
% 2.92/0.97  --qbf_mode                              false
% 2.92/0.97  --qbf_elim_univ                         false
% 2.92/0.97  --qbf_dom_inst                          none
% 2.92/0.97  --qbf_dom_pre_inst                      false
% 2.92/0.97  --qbf_sk_in                             false
% 2.92/0.97  --qbf_pred_elim                         true
% 2.92/0.97  --qbf_split                             512
% 2.92/0.97  
% 2.92/0.97  ------ BMC1 Options
% 2.92/0.97  
% 2.92/0.97  --bmc1_incremental                      false
% 2.92/0.97  --bmc1_axioms                           reachable_all
% 2.92/0.97  --bmc1_min_bound                        0
% 2.92/0.97  --bmc1_max_bound                        -1
% 2.92/0.97  --bmc1_max_bound_default                -1
% 2.92/0.97  --bmc1_symbol_reachability              true
% 2.92/0.97  --bmc1_property_lemmas                  false
% 2.92/0.97  --bmc1_k_induction                      false
% 2.92/0.97  --bmc1_non_equiv_states                 false
% 2.92/0.97  --bmc1_deadlock                         false
% 2.92/0.97  --bmc1_ucm                              false
% 2.92/0.97  --bmc1_add_unsat_core                   none
% 2.92/0.97  --bmc1_unsat_core_children              false
% 2.92/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.97  --bmc1_out_stat                         full
% 2.92/0.97  --bmc1_ground_init                      false
% 2.92/0.97  --bmc1_pre_inst_next_state              false
% 2.92/0.97  --bmc1_pre_inst_state                   false
% 2.92/0.97  --bmc1_pre_inst_reach_state             false
% 2.92/0.97  --bmc1_out_unsat_core                   false
% 2.92/0.97  --bmc1_aig_witness_out                  false
% 2.92/0.97  --bmc1_verbose                          false
% 2.92/0.97  --bmc1_dump_clauses_tptp                false
% 2.92/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.97  --bmc1_dump_file                        -
% 2.92/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.97  --bmc1_ucm_extend_mode                  1
% 2.92/0.97  --bmc1_ucm_init_mode                    2
% 2.92/0.97  --bmc1_ucm_cone_mode                    none
% 2.92/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.97  --bmc1_ucm_relax_model                  4
% 2.92/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.97  --bmc1_ucm_layered_model                none
% 2.92/0.97  --bmc1_ucm_max_lemma_size               10
% 2.92/0.97  
% 2.92/0.97  ------ AIG Options
% 2.92/0.97  
% 2.92/0.97  --aig_mode                              false
% 2.92/0.97  
% 2.92/0.97  ------ Instantiation Options
% 2.92/0.97  
% 2.92/0.97  --instantiation_flag                    true
% 2.92/0.97  --inst_sos_flag                         false
% 2.92/0.97  --inst_sos_phase                        true
% 2.92/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel_side                     num_symb
% 2.92/0.97  --inst_solver_per_active                1400
% 2.92/0.97  --inst_solver_calls_frac                1.
% 2.92/0.97  --inst_passive_queue_type               priority_queues
% 2.92/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.97  --inst_passive_queues_freq              [25;2]
% 2.92/0.97  --inst_dismatching                      true
% 2.92/0.97  --inst_eager_unprocessed_to_passive     true
% 2.92/0.97  --inst_prop_sim_given                   true
% 2.92/0.97  --inst_prop_sim_new                     false
% 2.92/0.97  --inst_subs_new                         false
% 2.92/0.97  --inst_eq_res_simp                      false
% 2.92/0.97  --inst_subs_given                       false
% 2.92/0.97  --inst_orphan_elimination               true
% 2.92/0.97  --inst_learning_loop_flag               true
% 2.92/0.97  --inst_learning_start                   3000
% 2.92/0.97  --inst_learning_factor                  2
% 2.92/0.97  --inst_start_prop_sim_after_learn       3
% 2.92/0.97  --inst_sel_renew                        solver
% 2.92/0.97  --inst_lit_activity_flag                true
% 2.92/0.97  --inst_restr_to_given                   false
% 2.92/0.97  --inst_activity_threshold               500
% 2.92/0.97  --inst_out_proof                        true
% 2.92/0.97  
% 2.92/0.97  ------ Resolution Options
% 2.92/0.97  
% 2.92/0.97  --resolution_flag                       true
% 2.92/0.97  --res_lit_sel                           adaptive
% 2.92/0.97  --res_lit_sel_side                      none
% 2.92/0.97  --res_ordering                          kbo
% 2.92/0.97  --res_to_prop_solver                    active
% 2.92/0.97  --res_prop_simpl_new                    false
% 2.92/0.97  --res_prop_simpl_given                  true
% 2.92/0.97  --res_passive_queue_type                priority_queues
% 2.92/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.97  --res_passive_queues_freq               [15;5]
% 2.92/0.97  --res_forward_subs                      full
% 2.92/0.97  --res_backward_subs                     full
% 2.92/0.97  --res_forward_subs_resolution           true
% 2.92/0.97  --res_backward_subs_resolution          true
% 2.92/0.97  --res_orphan_elimination                true
% 2.92/0.97  --res_time_limit                        2.
% 2.92/0.97  --res_out_proof                         true
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Options
% 2.92/0.97  
% 2.92/0.97  --superposition_flag                    true
% 2.92/0.97  --sup_passive_queue_type                priority_queues
% 2.92/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.97  --demod_completeness_check              fast
% 2.92/0.97  --demod_use_ground                      true
% 2.92/0.97  --sup_to_prop_solver                    passive
% 2.92/0.97  --sup_prop_simpl_new                    true
% 2.92/0.97  --sup_prop_simpl_given                  true
% 2.92/0.97  --sup_fun_splitting                     false
% 2.92/0.97  --sup_smt_interval                      50000
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Simplification Setup
% 2.92/0.97  
% 2.92/0.97  --sup_indices_passive                   []
% 2.92/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_full_bw                           [BwDemod]
% 2.92/0.97  --sup_immed_triv                        [TrivRules]
% 2.92/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_immed_bw_main                     []
% 2.92/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  
% 2.92/0.97  ------ Combination Options
% 2.92/0.97  
% 2.92/0.97  --comb_res_mult                         3
% 2.92/0.97  --comb_sup_mult                         2
% 2.92/0.97  --comb_inst_mult                        10
% 2.92/0.97  
% 2.92/0.97  ------ Debug Options
% 2.92/0.97  
% 2.92/0.97  --dbg_backtrace                         false
% 2.92/0.97  --dbg_dump_prop_clauses                 false
% 2.92/0.97  --dbg_dump_prop_clauses_file            -
% 2.92/0.97  --dbg_out_stat                          false
% 2.92/0.97  ------ Parsing...
% 2.92/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.97  ------ Proving...
% 2.92/0.97  ------ Problem Properties 
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  clauses                                 22
% 2.92/0.97  conjectures                             3
% 2.92/0.97  EPR                                     5
% 2.92/0.97  Horn                                    17
% 2.92/0.97  unary                                   8
% 2.92/0.97  binary                                  7
% 2.92/0.97  lits                                    44
% 2.92/0.97  lits eq                                 10
% 2.92/0.97  fd_pure                                 0
% 2.92/0.97  fd_pseudo                               0
% 2.92/0.97  fd_cond                                 0
% 2.92/0.97  fd_pseudo_cond                          4
% 2.92/0.97  AC symbols                              0
% 2.92/0.97  
% 2.92/0.97  ------ Schedule dynamic 5 is on 
% 2.92/0.97  
% 2.92/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  ------ 
% 2.92/0.97  Current options:
% 2.92/0.97  ------ 
% 2.92/0.97  
% 2.92/0.97  ------ Input Options
% 2.92/0.97  
% 2.92/0.97  --out_options                           all
% 2.92/0.97  --tptp_safe_out                         true
% 2.92/0.97  --problem_path                          ""
% 2.92/0.97  --include_path                          ""
% 2.92/0.97  --clausifier                            res/vclausify_rel
% 2.92/0.97  --clausifier_options                    --mode clausify
% 2.92/0.97  --stdin                                 false
% 2.92/0.97  --stats_out                             all
% 2.92/0.97  
% 2.92/0.97  ------ General Options
% 2.92/0.97  
% 2.92/0.97  --fof                                   false
% 2.92/0.97  --time_out_real                         305.
% 2.92/0.97  --time_out_virtual                      -1.
% 2.92/0.97  --symbol_type_check                     false
% 2.92/0.97  --clausify_out                          false
% 2.92/0.97  --sig_cnt_out                           false
% 2.92/0.97  --trig_cnt_out                          false
% 2.92/0.97  --trig_cnt_out_tolerance                1.
% 2.92/0.97  --trig_cnt_out_sk_spl                   false
% 2.92/0.97  --abstr_cl_out                          false
% 2.92/0.97  
% 2.92/0.97  ------ Global Options
% 2.92/0.97  
% 2.92/0.97  --schedule                              default
% 2.92/0.97  --add_important_lit                     false
% 2.92/0.97  --prop_solver_per_cl                    1000
% 2.92/0.97  --min_unsat_core                        false
% 2.92/0.97  --soft_assumptions                      false
% 2.92/0.97  --soft_lemma_size                       3
% 2.92/0.97  --prop_impl_unit_size                   0
% 2.92/0.97  --prop_impl_unit                        []
% 2.92/0.97  --share_sel_clauses                     true
% 2.92/0.97  --reset_solvers                         false
% 2.92/0.97  --bc_imp_inh                            [conj_cone]
% 2.92/0.97  --conj_cone_tolerance                   3.
% 2.92/0.97  --extra_neg_conj                        none
% 2.92/0.97  --large_theory_mode                     true
% 2.92/0.97  --prolific_symb_bound                   200
% 2.92/0.97  --lt_threshold                          2000
% 2.92/0.97  --clause_weak_htbl                      true
% 2.92/0.97  --gc_record_bc_elim                     false
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing Options
% 2.92/0.97  
% 2.92/0.97  --preprocessing_flag                    true
% 2.92/0.97  --time_out_prep_mult                    0.1
% 2.92/0.97  --splitting_mode                        input
% 2.92/0.97  --splitting_grd                         true
% 2.92/0.97  --splitting_cvd                         false
% 2.92/0.97  --splitting_cvd_svl                     false
% 2.92/0.97  --splitting_nvd                         32
% 2.92/0.97  --sub_typing                            true
% 2.92/0.97  --prep_gs_sim                           true
% 2.92/0.97  --prep_unflatten                        true
% 2.92/0.97  --prep_res_sim                          true
% 2.92/0.97  --prep_upred                            true
% 2.92/0.97  --prep_sem_filter                       exhaustive
% 2.92/0.97  --prep_sem_filter_out                   false
% 2.92/0.97  --pred_elim                             true
% 2.92/0.97  --res_sim_input                         true
% 2.92/0.97  --eq_ax_congr_red                       true
% 2.92/0.97  --pure_diseq_elim                       true
% 2.92/0.97  --brand_transform                       false
% 2.92/0.97  --non_eq_to_eq                          false
% 2.92/0.97  --prep_def_merge                        true
% 2.92/0.97  --prep_def_merge_prop_impl              false
% 2.92/0.97  --prep_def_merge_mbd                    true
% 2.92/0.97  --prep_def_merge_tr_red                 false
% 2.92/0.97  --prep_def_merge_tr_cl                  false
% 2.92/0.97  --smt_preprocessing                     true
% 2.92/0.97  --smt_ac_axioms                         fast
% 2.92/0.97  --preprocessed_out                      false
% 2.92/0.97  --preprocessed_stats                    false
% 2.92/0.97  
% 2.92/0.97  ------ Abstraction refinement Options
% 2.92/0.97  
% 2.92/0.97  --abstr_ref                             []
% 2.92/0.97  --abstr_ref_prep                        false
% 2.92/0.97  --abstr_ref_until_sat                   false
% 2.92/0.97  --abstr_ref_sig_restrict                funpre
% 2.92/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.97  --abstr_ref_under                       []
% 2.92/0.97  
% 2.92/0.97  ------ SAT Options
% 2.92/0.97  
% 2.92/0.97  --sat_mode                              false
% 2.92/0.97  --sat_fm_restart_options                ""
% 2.92/0.97  --sat_gr_def                            false
% 2.92/0.97  --sat_epr_types                         true
% 2.92/0.97  --sat_non_cyclic_types                  false
% 2.92/0.97  --sat_finite_models                     false
% 2.92/0.97  --sat_fm_lemmas                         false
% 2.92/0.97  --sat_fm_prep                           false
% 2.92/0.97  --sat_fm_uc_incr                        true
% 2.92/0.97  --sat_out_model                         small
% 2.92/0.97  --sat_out_clauses                       false
% 2.92/0.97  
% 2.92/0.97  ------ QBF Options
% 2.92/0.97  
% 2.92/0.97  --qbf_mode                              false
% 2.92/0.97  --qbf_elim_univ                         false
% 2.92/0.97  --qbf_dom_inst                          none
% 2.92/0.97  --qbf_dom_pre_inst                      false
% 2.92/0.97  --qbf_sk_in                             false
% 2.92/0.97  --qbf_pred_elim                         true
% 2.92/0.97  --qbf_split                             512
% 2.92/0.97  
% 2.92/0.97  ------ BMC1 Options
% 2.92/0.97  
% 2.92/0.97  --bmc1_incremental                      false
% 2.92/0.97  --bmc1_axioms                           reachable_all
% 2.92/0.97  --bmc1_min_bound                        0
% 2.92/0.97  --bmc1_max_bound                        -1
% 2.92/0.97  --bmc1_max_bound_default                -1
% 2.92/0.97  --bmc1_symbol_reachability              true
% 2.92/0.97  --bmc1_property_lemmas                  false
% 2.92/0.97  --bmc1_k_induction                      false
% 2.92/0.97  --bmc1_non_equiv_states                 false
% 2.92/0.97  --bmc1_deadlock                         false
% 2.92/0.97  --bmc1_ucm                              false
% 2.92/0.97  --bmc1_add_unsat_core                   none
% 2.92/0.97  --bmc1_unsat_core_children              false
% 2.92/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.97  --bmc1_out_stat                         full
% 2.92/0.97  --bmc1_ground_init                      false
% 2.92/0.97  --bmc1_pre_inst_next_state              false
% 2.92/0.97  --bmc1_pre_inst_state                   false
% 2.92/0.97  --bmc1_pre_inst_reach_state             false
% 2.92/0.97  --bmc1_out_unsat_core                   false
% 2.92/0.97  --bmc1_aig_witness_out                  false
% 2.92/0.97  --bmc1_verbose                          false
% 2.92/0.97  --bmc1_dump_clauses_tptp                false
% 2.92/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.97  --bmc1_dump_file                        -
% 2.92/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.97  --bmc1_ucm_extend_mode                  1
% 2.92/0.97  --bmc1_ucm_init_mode                    2
% 2.92/0.97  --bmc1_ucm_cone_mode                    none
% 2.92/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.97  --bmc1_ucm_relax_model                  4
% 2.92/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.97  --bmc1_ucm_layered_model                none
% 2.92/0.97  --bmc1_ucm_max_lemma_size               10
% 2.92/0.97  
% 2.92/0.97  ------ AIG Options
% 2.92/0.97  
% 2.92/0.97  --aig_mode                              false
% 2.92/0.97  
% 2.92/0.97  ------ Instantiation Options
% 2.92/0.97  
% 2.92/0.97  --instantiation_flag                    true
% 2.92/0.97  --inst_sos_flag                         false
% 2.92/0.97  --inst_sos_phase                        true
% 2.92/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel_side                     none
% 2.92/0.97  --inst_solver_per_active                1400
% 2.92/0.97  --inst_solver_calls_frac                1.
% 2.92/0.97  --inst_passive_queue_type               priority_queues
% 2.92/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.97  --inst_passive_queues_freq              [25;2]
% 2.92/0.97  --inst_dismatching                      true
% 2.92/0.97  --inst_eager_unprocessed_to_passive     true
% 2.92/0.97  --inst_prop_sim_given                   true
% 2.92/0.97  --inst_prop_sim_new                     false
% 2.92/0.97  --inst_subs_new                         false
% 2.92/0.97  --inst_eq_res_simp                      false
% 2.92/0.97  --inst_subs_given                       false
% 2.92/0.97  --inst_orphan_elimination               true
% 2.92/0.97  --inst_learning_loop_flag               true
% 2.92/0.97  --inst_learning_start                   3000
% 2.92/0.97  --inst_learning_factor                  2
% 2.92/0.97  --inst_start_prop_sim_after_learn       3
% 2.92/0.97  --inst_sel_renew                        solver
% 2.92/0.97  --inst_lit_activity_flag                true
% 2.92/0.97  --inst_restr_to_given                   false
% 2.92/0.97  --inst_activity_threshold               500
% 2.92/0.97  --inst_out_proof                        true
% 2.92/0.97  
% 2.92/0.97  ------ Resolution Options
% 2.92/0.97  
% 2.92/0.97  --resolution_flag                       false
% 2.92/0.97  --res_lit_sel                           adaptive
% 2.92/0.97  --res_lit_sel_side                      none
% 2.92/0.97  --res_ordering                          kbo
% 2.92/0.97  --res_to_prop_solver                    active
% 2.92/0.97  --res_prop_simpl_new                    false
% 2.92/0.97  --res_prop_simpl_given                  true
% 2.92/0.97  --res_passive_queue_type                priority_queues
% 2.92/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.97  --res_passive_queues_freq               [15;5]
% 2.92/0.97  --res_forward_subs                      full
% 2.92/0.97  --res_backward_subs                     full
% 2.92/0.97  --res_forward_subs_resolution           true
% 2.92/0.97  --res_backward_subs_resolution          true
% 2.92/0.97  --res_orphan_elimination                true
% 2.92/0.97  --res_time_limit                        2.
% 2.92/0.97  --res_out_proof                         true
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Options
% 2.92/0.97  
% 2.92/0.97  --superposition_flag                    true
% 2.92/0.97  --sup_passive_queue_type                priority_queues
% 2.92/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.97  --demod_completeness_check              fast
% 2.92/0.97  --demod_use_ground                      true
% 2.92/0.97  --sup_to_prop_solver                    passive
% 2.92/0.97  --sup_prop_simpl_new                    true
% 2.92/0.97  --sup_prop_simpl_given                  true
% 2.92/0.97  --sup_fun_splitting                     false
% 2.92/0.97  --sup_smt_interval                      50000
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Simplification Setup
% 2.92/0.97  
% 2.92/0.97  --sup_indices_passive                   []
% 2.92/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_full_bw                           [BwDemod]
% 2.92/0.97  --sup_immed_triv                        [TrivRules]
% 2.92/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_immed_bw_main                     []
% 2.92/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  
% 2.92/0.97  ------ Combination Options
% 2.92/0.97  
% 2.92/0.97  --comb_res_mult                         3
% 2.92/0.97  --comb_sup_mult                         2
% 2.92/0.97  --comb_inst_mult                        10
% 2.92/0.97  
% 2.92/0.97  ------ Debug Options
% 2.92/0.97  
% 2.92/0.97  --dbg_backtrace                         false
% 2.92/0.97  --dbg_dump_prop_clauses                 false
% 2.92/0.97  --dbg_dump_prop_clauses_file            -
% 2.92/0.97  --dbg_out_stat                          false
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  ------ Proving...
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  % SZS status Theorem for theBenchmark.p
% 2.92/0.97  
% 2.92/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.97  
% 2.92/0.97  fof(f16,conjecture,(
% 2.92/0.97    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f17,negated_conjecture,(
% 2.92/0.97    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 2.92/0.97    inference(negated_conjecture,[],[f16])).
% 2.92/0.97  
% 2.92/0.97  fof(f20,plain,(
% 2.92/0.97    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 2.92/0.97    inference(ennf_transformation,[],[f17])).
% 2.92/0.97  
% 2.92/0.97  fof(f21,plain,(
% 2.92/0.97    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 2.92/0.97    inference(flattening,[],[f20])).
% 2.92/0.97  
% 2.92/0.97  fof(f35,plain,(
% 2.92/0.97    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_xboole_0(k2_tarski(sK2,sK4),sK3) != sK3 & r2_hidden(sK4,sK3) & r2_hidden(sK2,sK3))),
% 2.92/0.97    introduced(choice_axiom,[])).
% 2.92/0.97  
% 2.92/0.97  fof(f36,plain,(
% 2.92/0.97    k2_xboole_0(k2_tarski(sK2,sK4),sK3) != sK3 & r2_hidden(sK4,sK3) & r2_hidden(sK2,sK3)),
% 2.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f35])).
% 2.92/0.97  
% 2.92/0.97  fof(f64,plain,(
% 2.92/0.97    r2_hidden(sK4,sK3)),
% 2.92/0.97    inference(cnf_transformation,[],[f36])).
% 2.92/0.97  
% 2.92/0.97  fof(f63,plain,(
% 2.92/0.97    r2_hidden(sK2,sK3)),
% 2.92/0.97    inference(cnf_transformation,[],[f36])).
% 2.92/0.97  
% 2.92/0.97  fof(f15,axiom,(
% 2.92/0.97    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f33,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.92/0.97    inference(nnf_transformation,[],[f15])).
% 2.92/0.97  
% 2.92/0.97  fof(f34,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.92/0.97    inference(flattening,[],[f33])).
% 2.92/0.97  
% 2.92/0.97  fof(f62,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f34])).
% 2.92/0.97  
% 2.92/0.97  fof(f10,axiom,(
% 2.92/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f55,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f10])).
% 2.92/0.97  
% 2.92/0.97  fof(f11,axiom,(
% 2.92/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f56,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f11])).
% 2.92/0.97  
% 2.92/0.97  fof(f12,axiom,(
% 2.92/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f57,plain,(
% 2.92/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f12])).
% 2.92/0.97  
% 2.92/0.97  fof(f13,axiom,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f58,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f13])).
% 2.92/0.97  
% 2.92/0.97  fof(f66,plain,(
% 2.92/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f57,f58])).
% 2.92/0.97  
% 2.92/0.97  fof(f67,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f56,f66])).
% 2.92/0.97  
% 2.92/0.97  fof(f68,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f55,f67])).
% 2.92/0.97  
% 2.92/0.97  fof(f79,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f62,f68])).
% 2.92/0.97  
% 2.92/0.97  fof(f6,axiom,(
% 2.92/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f19,plain,(
% 2.92/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.92/0.97    inference(ennf_transformation,[],[f6])).
% 2.92/0.97  
% 2.92/0.97  fof(f51,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f19])).
% 2.92/0.97  
% 2.92/0.97  fof(f7,axiom,(
% 2.92/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f52,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f7])).
% 2.92/0.97  
% 2.92/0.97  fof(f14,axiom,(
% 2.92/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f59,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f14])).
% 2.92/0.97  
% 2.92/0.97  fof(f69,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.92/0.97    inference(definition_unfolding,[],[f59,f68])).
% 2.92/0.97  
% 2.92/0.97  fof(f4,axiom,(
% 2.92/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f49,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f4])).
% 2.92/0.97  
% 2.92/0.97  fof(f77,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.92/0.97    inference(definition_unfolding,[],[f52,f69,f69,f49])).
% 2.92/0.97  
% 2.92/0.97  fof(f5,axiom,(
% 2.92/0.97    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f50,plain,(
% 2.92/0.97    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.92/0.97    inference(cnf_transformation,[],[f5])).
% 2.92/0.97  
% 2.92/0.97  fof(f76,plain,(
% 2.92/0.97    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 2.92/0.97    inference(definition_unfolding,[],[f50,f69])).
% 2.92/0.97  
% 2.92/0.97  fof(f2,axiom,(
% 2.92/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f26,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.97    inference(nnf_transformation,[],[f2])).
% 2.92/0.97  
% 2.92/0.97  fof(f27,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.97    inference(flattening,[],[f26])).
% 2.92/0.97  
% 2.92/0.97  fof(f28,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.97    inference(rectify,[],[f27])).
% 2.92/0.97  
% 2.92/0.97  fof(f29,plain,(
% 2.92/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.92/0.97    introduced(choice_axiom,[])).
% 2.92/0.97  
% 2.92/0.97  fof(f30,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 2.92/0.97  
% 2.92/0.97  fof(f43,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f30])).
% 2.92/0.97  
% 2.92/0.97  fof(f72,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f43,f49])).
% 2.92/0.97  
% 2.92/0.97  fof(f9,axiom,(
% 2.92/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f54,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f9])).
% 2.92/0.97  
% 2.92/0.97  fof(f78,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f54,f68,f68])).
% 2.92/0.97  
% 2.92/0.97  fof(f3,axiom,(
% 2.92/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f31,plain,(
% 2.92/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.92/0.97    inference(nnf_transformation,[],[f3])).
% 2.92/0.97  
% 2.92/0.97  fof(f32,plain,(
% 2.92/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.92/0.97    inference(flattening,[],[f31])).
% 2.92/0.97  
% 2.92/0.97  fof(f47,plain,(
% 2.92/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.92/0.97    inference(cnf_transformation,[],[f32])).
% 2.92/0.97  
% 2.92/0.97  fof(f86,plain,(
% 2.92/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.92/0.97    inference(equality_resolution,[],[f47])).
% 2.92/0.97  
% 2.92/0.97  fof(f60,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f34])).
% 2.92/0.97  
% 2.92/0.97  fof(f81,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f60,f68])).
% 2.92/0.97  
% 2.92/0.97  fof(f41,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.92/0.97    inference(cnf_transformation,[],[f30])).
% 2.92/0.97  
% 2.92/0.97  fof(f74,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.92/0.97    inference(definition_unfolding,[],[f41,f49])).
% 2.92/0.97  
% 2.92/0.97  fof(f84,plain,(
% 2.92/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.92/0.97    inference(equality_resolution,[],[f74])).
% 2.92/0.97  
% 2.92/0.97  fof(f1,axiom,(
% 2.92/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f18,plain,(
% 2.92/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.92/0.97    inference(ennf_transformation,[],[f1])).
% 2.92/0.97  
% 2.92/0.97  fof(f22,plain,(
% 2.92/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.92/0.97    inference(nnf_transformation,[],[f18])).
% 2.92/0.97  
% 2.92/0.97  fof(f23,plain,(
% 2.92/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.92/0.97    inference(rectify,[],[f22])).
% 2.92/0.97  
% 2.92/0.97  fof(f24,plain,(
% 2.92/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.92/0.97    introduced(choice_axiom,[])).
% 2.92/0.97  
% 2.92/0.97  fof(f25,plain,(
% 2.92/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.92/0.97  
% 2.92/0.97  fof(f38,plain,(
% 2.92/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f25])).
% 2.92/0.97  
% 2.92/0.97  fof(f8,axiom,(
% 2.92/0.97    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f53,plain,(
% 2.92/0.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.92/0.97    inference(cnf_transformation,[],[f8])).
% 2.92/0.97  
% 2.92/0.97  fof(f40,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.92/0.97    inference(cnf_transformation,[],[f30])).
% 2.92/0.97  
% 2.92/0.97  fof(f75,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.92/0.97    inference(definition_unfolding,[],[f40,f49])).
% 2.92/0.97  
% 2.92/0.97  fof(f85,plain,(
% 2.92/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.92/0.98    inference(equality_resolution,[],[f75])).
% 2.92/0.98  
% 2.92/0.98  fof(f65,plain,(
% 2.92/0.98    k2_xboole_0(k2_tarski(sK2,sK4),sK3) != sK3),
% 2.92/0.98    inference(cnf_transformation,[],[f36])).
% 2.92/0.98  
% 2.92/0.98  fof(f82,plain,(
% 2.92/0.98    k3_tarski(k4_enumset1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),sK3)) != sK3),
% 2.92/0.98    inference(definition_unfolding,[],[f65,f69,f68])).
% 2.92/0.98  
% 2.92/0.98  cnf(c_21,negated_conjecture,
% 2.92/0.98      ( r2_hidden(sK4,sK3) ),
% 2.92/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_608,plain,
% 2.92/0.98      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_22,negated_conjecture,
% 2.92/0.98      ( r2_hidden(sK2,sK3) ),
% 2.92/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_607,plain,
% 2.92/0.98      ( r2_hidden(sK2,sK3) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_17,plain,
% 2.92/0.98      ( ~ r2_hidden(X0,X1)
% 2.92/0.98      | ~ r2_hidden(X2,X1)
% 2.92/0.98      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
% 2.92/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_611,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.92/0.98      | r2_hidden(X2,X1) != iProver_top
% 2.92/0.98      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_13,plain,
% 2.92/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.92/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_612,plain,
% 2.92/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2657,plain,
% 2.92/0.98      ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) = k4_enumset1(X0,X0,X0,X0,X0,X1)
% 2.92/0.98      | r2_hidden(X1,X2) != iProver_top
% 2.92/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_611,c_612]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_3606,plain,
% 2.92/0.98      ( k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,X0),sK3) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,X0)
% 2.92/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_607,c_2657]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_5013,plain,
% 2.92/0.98      ( k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),sK3) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4) ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_608,c_3606]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_14,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 2.92/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_5074,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4)))) = k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4))) ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_5013,c_14]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_12,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 2.92/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_5,plain,
% 2.92/0.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 2.92/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.92/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 2.92/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_618,plain,
% 2.92/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 2.92/0.98      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 2.92/0.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_16,plain,
% 2.92/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
% 2.92/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_10,plain,
% 2.92/0.98      ( r1_tarski(X0,X0) ),
% 2.92/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_613,plain,
% 2.92/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_19,plain,
% 2.92/0.98      ( r2_hidden(X0,X1)
% 2.92/0.98      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 2.92/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_609,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.92/0.98      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_993,plain,
% 2.92/0.98      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_613,c_609]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1309,plain,
% 2.92/0.98      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_16,c_993]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1001,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_16,c_12]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1162,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_1001,c_14]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1163,plain,
% 2.92/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_1162,c_1001]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_7,plain,
% 2.92/0.98      ( ~ r2_hidden(X0,X1)
% 2.92/0.98      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.92/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_616,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.92/0.98      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1829,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.92/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_1163,c_616]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2329,plain,
% 2.92/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_1309,c_1829]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2782,plain,
% 2.92/0.98      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 2.92/0.98      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_618,c_2329]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1,plain,
% 2.92/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.92/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_622,plain,
% 2.92/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.92/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2340,plain,
% 2.92/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_622,c_2329]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2423,plain,
% 2.92/0.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_2340,c_612]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2792,plain,
% 2.92/0.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
% 2.92/0.98      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_2782,c_2423]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_15,plain,
% 2.92/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.92/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2793,plain,
% 2.92/0.98      ( k1_xboole_0 = X0
% 2.92/0.98      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 2.92/0.98      inference(demodulation,[status(thm)],[c_2792,c_15]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_910,plain,
% 2.92/0.98      ( k3_xboole_0(X0,X0) = X0 ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_613,c_612]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1830,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.92/0.98      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_910,c_616]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_8,plain,
% 2.92/0.98      ( r2_hidden(X0,X1)
% 2.92/0.98      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.92/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_615,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.92/0.98      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1512,plain,
% 2.92/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.92/0.98      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_910,c_615]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_3261,plain,
% 2.92/0.98      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_1830,c_1512]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_3271,plain,
% 2.92/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_2793,c_3261]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_5076,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4))) = sK3 ),
% 2.92/0.98      inference(demodulation,[status(thm)],[c_5074,c_12,c_3271]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_20,negated_conjecture,
% 2.92/0.98      ( k3_tarski(k4_enumset1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4),sK3)) != sK3 ),
% 2.92/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_998,plain,
% 2.92/0.98      ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK4))) != sK3 ),
% 2.92/0.98      inference(demodulation,[status(thm)],[c_16,c_20]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(contradiction,plain,
% 2.92/0.98      ( $false ),
% 2.92/0.98      inference(minisat,[status(thm)],[c_5076,c_998]) ).
% 2.92/0.98  
% 2.92/0.98  
% 2.92/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/0.98  
% 2.92/0.98  ------                               Statistics
% 2.92/0.98  
% 2.92/0.98  ------ General
% 2.92/0.98  
% 2.92/0.98  abstr_ref_over_cycles:                  0
% 2.92/0.98  abstr_ref_under_cycles:                 0
% 2.92/0.98  gc_basic_clause_elim:                   0
% 2.92/0.98  forced_gc_time:                         0
% 2.92/0.98  parsing_time:                           0.008
% 2.92/0.98  unif_index_cands_time:                  0.
% 2.92/0.98  unif_index_add_time:                    0.
% 2.92/0.98  orderings_time:                         0.
% 2.92/0.98  out_proof_time:                         0.007
% 2.92/0.98  total_time:                             0.184
% 2.92/0.98  num_of_symbols:                         43
% 2.92/0.98  num_of_terms:                           5752
% 2.92/0.98  
% 2.92/0.98  ------ Preprocessing
% 2.92/0.98  
% 2.92/0.98  num_of_splits:                          0
% 2.92/0.98  num_of_split_atoms:                     0
% 2.92/0.98  num_of_reused_defs:                     0
% 2.92/0.98  num_eq_ax_congr_red:                    27
% 2.92/0.98  num_of_sem_filtered_clauses:            1
% 2.92/0.98  num_of_subtypes:                        0
% 2.92/0.98  monotx_restored_types:                  0
% 2.92/0.98  sat_num_of_epr_types:                   0
% 2.92/0.98  sat_num_of_non_cyclic_types:            0
% 2.92/0.98  sat_guarded_non_collapsed_types:        0
% 2.92/0.98  num_pure_diseq_elim:                    0
% 2.92/0.98  simp_replaced_by:                       0
% 2.92/0.98  res_preprocessed:                       103
% 2.92/0.98  prep_upred:                             0
% 2.92/0.98  prep_unflattend:                        0
% 2.92/0.98  smt_new_axioms:                         0
% 2.92/0.98  pred_elim_cands:                        2
% 2.92/0.98  pred_elim:                              0
% 2.92/0.98  pred_elim_cl:                           0
% 2.92/0.98  pred_elim_cycles:                       2
% 2.92/0.98  merged_defs:                            0
% 2.92/0.98  merged_defs_ncl:                        0
% 2.92/0.98  bin_hyper_res:                          0
% 2.92/0.98  prep_cycles:                            4
% 2.92/0.98  pred_elim_time:                         0.
% 2.92/0.98  splitting_time:                         0.
% 2.92/0.98  sem_filter_time:                        0.
% 2.92/0.98  monotx_time:                            0.001
% 2.92/0.98  subtype_inf_time:                       0.
% 2.92/0.98  
% 2.92/0.98  ------ Problem properties
% 2.92/0.98  
% 2.92/0.98  clauses:                                22
% 2.92/0.98  conjectures:                            3
% 2.92/0.98  epr:                                    5
% 2.92/0.98  horn:                                   17
% 2.92/0.98  ground:                                 3
% 2.92/0.98  unary:                                  8
% 2.92/0.98  binary:                                 7
% 2.92/0.98  lits:                                   44
% 2.92/0.98  lits_eq:                                10
% 2.92/0.98  fd_pure:                                0
% 2.92/0.98  fd_pseudo:                              0
% 2.92/0.98  fd_cond:                                0
% 2.92/0.98  fd_pseudo_cond:                         4
% 2.92/0.98  ac_symbols:                             0
% 2.92/0.98  
% 2.92/0.98  ------ Propositional Solver
% 2.92/0.98  
% 2.92/0.98  prop_solver_calls:                      28
% 2.92/0.98  prop_fast_solver_calls:                 535
% 2.92/0.98  smt_solver_calls:                       0
% 2.92/0.98  smt_fast_solver_calls:                  0
% 2.92/0.98  prop_num_of_clauses:                    2023
% 2.92/0.98  prop_preprocess_simplified:             6088
% 2.92/0.98  prop_fo_subsumed:                       1
% 2.92/0.98  prop_solver_time:                       0.
% 2.92/0.98  smt_solver_time:                        0.
% 2.92/0.98  smt_fast_solver_time:                   0.
% 2.92/0.98  prop_fast_solver_time:                  0.
% 2.92/0.98  prop_unsat_core_time:                   0.
% 2.92/0.98  
% 2.92/0.98  ------ QBF
% 2.92/0.98  
% 2.92/0.98  qbf_q_res:                              0
% 2.92/0.98  qbf_num_tautologies:                    0
% 2.92/0.98  qbf_prep_cycles:                        0
% 2.92/0.98  
% 2.92/0.98  ------ BMC1
% 2.92/0.98  
% 2.92/0.98  bmc1_current_bound:                     -1
% 2.92/0.98  bmc1_last_solved_bound:                 -1
% 2.92/0.98  bmc1_unsat_core_size:                   -1
% 2.92/0.98  bmc1_unsat_core_parents_size:           -1
% 2.92/0.98  bmc1_merge_next_fun:                    0
% 2.92/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.92/0.98  
% 2.92/0.98  ------ Instantiation
% 2.92/0.98  
% 2.92/0.98  inst_num_of_clauses:                    565
% 2.92/0.98  inst_num_in_passive:                    287
% 2.92/0.98  inst_num_in_active:                     219
% 2.92/0.98  inst_num_in_unprocessed:                59
% 2.92/0.98  inst_num_of_loops:                      270
% 2.92/0.98  inst_num_of_learning_restarts:          0
% 2.92/0.98  inst_num_moves_active_passive:          49
% 2.92/0.98  inst_lit_activity:                      0
% 2.92/0.98  inst_lit_activity_moves:                0
% 2.92/0.98  inst_num_tautologies:                   0
% 2.92/0.98  inst_num_prop_implied:                  0
% 2.92/0.98  inst_num_existing_simplified:           0
% 2.92/0.98  inst_num_eq_res_simplified:             0
% 2.92/0.98  inst_num_child_elim:                    0
% 2.92/0.98  inst_num_of_dismatching_blockings:      193
% 2.92/0.98  inst_num_of_non_proper_insts:           501
% 2.92/0.98  inst_num_of_duplicates:                 0
% 2.92/0.98  inst_inst_num_from_inst_to_res:         0
% 2.92/0.98  inst_dismatching_checking_time:         0.
% 2.92/0.98  
% 2.92/0.98  ------ Resolution
% 2.92/0.98  
% 2.92/0.98  res_num_of_clauses:                     0
% 2.92/0.98  res_num_in_passive:                     0
% 2.92/0.98  res_num_in_active:                      0
% 2.92/0.98  res_num_of_loops:                       107
% 2.92/0.98  res_forward_subset_subsumed:            27
% 2.92/0.98  res_backward_subset_subsumed:           0
% 2.92/0.98  res_forward_subsumed:                   0
% 2.92/0.98  res_backward_subsumed:                  0
% 2.92/0.98  res_forward_subsumption_resolution:     0
% 2.92/0.98  res_backward_subsumption_resolution:    0
% 2.92/0.98  res_clause_to_clause_subsumption:       524
% 2.92/0.98  res_orphan_elimination:                 0
% 2.92/0.98  res_tautology_del:                      33
% 2.92/0.98  res_num_eq_res_simplified:              0
% 2.92/0.98  res_num_sel_changes:                    0
% 2.92/0.98  res_moves_from_active_to_pass:          0
% 2.92/0.98  
% 2.92/0.98  ------ Superposition
% 2.92/0.98  
% 2.92/0.98  sup_time_total:                         0.
% 2.92/0.98  sup_time_generating:                    0.
% 2.92/0.98  sup_time_sim_full:                      0.
% 2.92/0.98  sup_time_sim_immed:                     0.
% 2.92/0.98  
% 2.92/0.98  sup_num_of_clauses:                     107
% 2.92/0.98  sup_num_in_active:                      49
% 2.92/0.98  sup_num_in_passive:                     58
% 2.92/0.98  sup_num_of_loops:                       53
% 2.92/0.98  sup_fw_superposition:                   108
% 2.92/0.98  sup_bw_superposition:                   98
% 2.92/0.98  sup_immediate_simplified:               97
% 2.92/0.98  sup_given_eliminated:                   2
% 2.92/0.98  comparisons_done:                       0
% 2.92/0.98  comparisons_avoided:                    0
% 2.92/0.98  
% 2.92/0.98  ------ Simplifications
% 2.92/0.98  
% 2.92/0.98  
% 2.92/0.98  sim_fw_subset_subsumed:                 5
% 2.92/0.98  sim_bw_subset_subsumed:                 1
% 2.92/0.98  sim_fw_subsumed:                        33
% 2.92/0.98  sim_bw_subsumed:                        1
% 2.92/0.98  sim_fw_subsumption_res:                 0
% 2.92/0.98  sim_bw_subsumption_res:                 0
% 2.92/0.98  sim_tautology_del:                      11
% 2.92/0.98  sim_eq_tautology_del:                   19
% 2.92/0.98  sim_eq_res_simp:                        1
% 2.92/0.98  sim_fw_demodulated:                     56
% 2.92/0.98  sim_bw_demodulated:                     4
% 2.92/0.98  sim_light_normalised:                   41
% 2.92/0.98  sim_joinable_taut:                      0
% 2.92/0.98  sim_joinable_simp:                      0
% 2.92/0.98  sim_ac_normalised:                      0
% 2.92/0.98  sim_smt_subsumption:                    0
% 2.92/0.98  
%------------------------------------------------------------------------------
