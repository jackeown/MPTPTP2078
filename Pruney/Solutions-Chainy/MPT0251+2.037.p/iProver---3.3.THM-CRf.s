%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:07 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 590 expanded)
%              Number of clauses        :   51 ( 171 expanded)
%              Number of leaves         :   21 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  317 (1948 expanded)
%              Number of equality atoms :  117 ( 603 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f39])).

fof(f69,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f58,f73,f73,f55])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f60,f72,f72])).

fof(f70,plain,(
    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f87,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(definition_unfolding,[],[f70,f73,f74])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_666,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_669,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_670,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2657,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_669,c_670])).

cnf(c_11369,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,X0),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_666,c_2657])).

cnf(c_11659,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_666,c_11369])).

cnf(c_16,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11782,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_11659,c_16])).

cnf(c_14,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_676,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_671,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1020,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_671,c_670])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_673,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2033,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_673])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_674,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2669,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_674])).

cnf(c_5507,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2033,c_2669])).

cnf(c_5515,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,X2)
    | r2_hidden(sK1(X0,X1,k5_xboole_0(X2,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_5507])).

cnf(c_10356,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X2,X2) ),
    inference(superposition,[status(thm)],[c_5515,c_5507])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_680,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | r2_hidden(sK2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_665,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(sK2(X1,X2),k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1299,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1,X1),k3_xboole_0(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_665])).

cnf(c_1300,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1299,c_1020])).

cnf(c_2509,plain,
    ( r2_hidden(sK2(X0,X0),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_1300])).

cnf(c_4400,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK2(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2509,c_670])).

cnf(c_5516,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4400,c_5507])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_664,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_1141,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_664])).

cnf(c_3875,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_1141])).

cnf(c_5555,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3875,c_5507])).

cnf(c_5556,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5555,c_5516])).

cnf(c_10357,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10356,c_5516,c_5556])).

cnf(c_11788,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
    inference(demodulation,[status(thm)],[c_11782,c_14,c_10357])).

cnf(c_18,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1304,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
    inference(demodulation,[status(thm)],[c_18,c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11788,c_1304])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.17/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.17/1.00  
% 4.17/1.00  ------  iProver source info
% 4.17/1.00  
% 4.17/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.17/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.17/1.00  git: non_committed_changes: false
% 4.17/1.00  git: last_make_outside_of_git: false
% 4.17/1.00  
% 4.17/1.00  ------ 
% 4.17/1.00  
% 4.17/1.00  ------ Input Options
% 4.17/1.00  
% 4.17/1.00  --out_options                           all
% 4.17/1.00  --tptp_safe_out                         true
% 4.17/1.00  --problem_path                          ""
% 4.17/1.00  --include_path                          ""
% 4.17/1.00  --clausifier                            res/vclausify_rel
% 4.17/1.00  --clausifier_options                    ""
% 4.17/1.00  --stdin                                 false
% 4.17/1.00  --stats_out                             all
% 4.17/1.00  
% 4.17/1.00  ------ General Options
% 4.17/1.00  
% 4.17/1.00  --fof                                   false
% 4.17/1.00  --time_out_real                         305.
% 4.17/1.00  --time_out_virtual                      -1.
% 4.17/1.00  --symbol_type_check                     false
% 4.17/1.00  --clausify_out                          false
% 4.17/1.00  --sig_cnt_out                           false
% 4.17/1.00  --trig_cnt_out                          false
% 4.17/1.00  --trig_cnt_out_tolerance                1.
% 4.17/1.00  --trig_cnt_out_sk_spl                   false
% 4.17/1.00  --abstr_cl_out                          false
% 4.17/1.00  
% 4.17/1.00  ------ Global Options
% 4.17/1.00  
% 4.17/1.00  --schedule                              default
% 4.17/1.00  --add_important_lit                     false
% 4.17/1.00  --prop_solver_per_cl                    1000
% 4.17/1.00  --min_unsat_core                        false
% 4.17/1.00  --soft_assumptions                      false
% 4.17/1.00  --soft_lemma_size                       3
% 4.17/1.00  --prop_impl_unit_size                   0
% 4.17/1.00  --prop_impl_unit                        []
% 4.17/1.00  --share_sel_clauses                     true
% 4.17/1.00  --reset_solvers                         false
% 4.17/1.00  --bc_imp_inh                            [conj_cone]
% 4.17/1.00  --conj_cone_tolerance                   3.
% 4.17/1.00  --extra_neg_conj                        none
% 4.17/1.00  --large_theory_mode                     true
% 4.17/1.00  --prolific_symb_bound                   200
% 4.17/1.00  --lt_threshold                          2000
% 4.17/1.00  --clause_weak_htbl                      true
% 4.17/1.00  --gc_record_bc_elim                     false
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing Options
% 4.17/1.00  
% 4.17/1.00  --preprocessing_flag                    true
% 4.17/1.00  --time_out_prep_mult                    0.1
% 4.17/1.00  --splitting_mode                        input
% 4.17/1.00  --splitting_grd                         true
% 4.17/1.00  --splitting_cvd                         false
% 4.17/1.00  --splitting_cvd_svl                     false
% 4.17/1.00  --splitting_nvd                         32
% 4.17/1.00  --sub_typing                            true
% 4.17/1.00  --prep_gs_sim                           true
% 4.17/1.00  --prep_unflatten                        true
% 4.17/1.00  --prep_res_sim                          true
% 4.17/1.00  --prep_upred                            true
% 4.17/1.00  --prep_sem_filter                       exhaustive
% 4.17/1.00  --prep_sem_filter_out                   false
% 4.17/1.00  --pred_elim                             true
% 4.17/1.00  --res_sim_input                         true
% 4.17/1.00  --eq_ax_congr_red                       true
% 4.17/1.00  --pure_diseq_elim                       true
% 4.17/1.00  --brand_transform                       false
% 4.17/1.00  --non_eq_to_eq                          false
% 4.17/1.00  --prep_def_merge                        true
% 4.17/1.00  --prep_def_merge_prop_impl              false
% 4.17/1.00  --prep_def_merge_mbd                    true
% 4.17/1.00  --prep_def_merge_tr_red                 false
% 4.17/1.00  --prep_def_merge_tr_cl                  false
% 4.17/1.00  --smt_preprocessing                     true
% 4.17/1.00  --smt_ac_axioms                         fast
% 4.17/1.00  --preprocessed_out                      false
% 4.17/1.00  --preprocessed_stats                    false
% 4.17/1.00  
% 4.17/1.00  ------ Abstraction refinement Options
% 4.17/1.00  
% 4.17/1.00  --abstr_ref                             []
% 4.17/1.00  --abstr_ref_prep                        false
% 4.17/1.00  --abstr_ref_until_sat                   false
% 4.17/1.00  --abstr_ref_sig_restrict                funpre
% 4.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.17/1.00  --abstr_ref_under                       []
% 4.17/1.00  
% 4.17/1.00  ------ SAT Options
% 4.17/1.00  
% 4.17/1.00  --sat_mode                              false
% 4.17/1.00  --sat_fm_restart_options                ""
% 4.17/1.00  --sat_gr_def                            false
% 4.17/1.00  --sat_epr_types                         true
% 4.17/1.00  --sat_non_cyclic_types                  false
% 4.17/1.00  --sat_finite_models                     false
% 4.17/1.00  --sat_fm_lemmas                         false
% 4.17/1.00  --sat_fm_prep                           false
% 4.17/1.00  --sat_fm_uc_incr                        true
% 4.17/1.00  --sat_out_model                         small
% 4.17/1.00  --sat_out_clauses                       false
% 4.17/1.00  
% 4.17/1.00  ------ QBF Options
% 4.17/1.00  
% 4.17/1.00  --qbf_mode                              false
% 4.17/1.00  --qbf_elim_univ                         false
% 4.17/1.00  --qbf_dom_inst                          none
% 4.17/1.00  --qbf_dom_pre_inst                      false
% 4.17/1.00  --qbf_sk_in                             false
% 4.17/1.00  --qbf_pred_elim                         true
% 4.17/1.00  --qbf_split                             512
% 4.17/1.00  
% 4.17/1.00  ------ BMC1 Options
% 4.17/1.00  
% 4.17/1.00  --bmc1_incremental                      false
% 4.17/1.00  --bmc1_axioms                           reachable_all
% 4.17/1.00  --bmc1_min_bound                        0
% 4.17/1.00  --bmc1_max_bound                        -1
% 4.17/1.00  --bmc1_max_bound_default                -1
% 4.17/1.00  --bmc1_symbol_reachability              true
% 4.17/1.00  --bmc1_property_lemmas                  false
% 4.17/1.00  --bmc1_k_induction                      false
% 4.17/1.00  --bmc1_non_equiv_states                 false
% 4.17/1.00  --bmc1_deadlock                         false
% 4.17/1.00  --bmc1_ucm                              false
% 4.17/1.00  --bmc1_add_unsat_core                   none
% 4.17/1.00  --bmc1_unsat_core_children              false
% 4.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.17/1.00  --bmc1_out_stat                         full
% 4.17/1.00  --bmc1_ground_init                      false
% 4.17/1.00  --bmc1_pre_inst_next_state              false
% 4.17/1.00  --bmc1_pre_inst_state                   false
% 4.17/1.00  --bmc1_pre_inst_reach_state             false
% 4.17/1.00  --bmc1_out_unsat_core                   false
% 4.17/1.00  --bmc1_aig_witness_out                  false
% 4.17/1.00  --bmc1_verbose                          false
% 4.17/1.00  --bmc1_dump_clauses_tptp                false
% 4.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.17/1.00  --bmc1_dump_file                        -
% 4.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.17/1.00  --bmc1_ucm_extend_mode                  1
% 4.17/1.00  --bmc1_ucm_init_mode                    2
% 4.17/1.00  --bmc1_ucm_cone_mode                    none
% 4.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.17/1.00  --bmc1_ucm_relax_model                  4
% 4.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.17/1.00  --bmc1_ucm_layered_model                none
% 4.17/1.00  --bmc1_ucm_max_lemma_size               10
% 4.17/1.00  
% 4.17/1.00  ------ AIG Options
% 4.17/1.00  
% 4.17/1.00  --aig_mode                              false
% 4.17/1.00  
% 4.17/1.00  ------ Instantiation Options
% 4.17/1.00  
% 4.17/1.00  --instantiation_flag                    true
% 4.17/1.00  --inst_sos_flag                         true
% 4.17/1.00  --inst_sos_phase                        true
% 4.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.17/1.00  --inst_lit_sel_side                     num_symb
% 4.17/1.00  --inst_solver_per_active                1400
% 4.17/1.00  --inst_solver_calls_frac                1.
% 4.17/1.00  --inst_passive_queue_type               priority_queues
% 4.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.17/1.00  --inst_passive_queues_freq              [25;2]
% 4.17/1.00  --inst_dismatching                      true
% 4.17/1.00  --inst_eager_unprocessed_to_passive     true
% 4.17/1.00  --inst_prop_sim_given                   true
% 4.17/1.00  --inst_prop_sim_new                     false
% 4.17/1.00  --inst_subs_new                         false
% 4.17/1.00  --inst_eq_res_simp                      false
% 4.17/1.00  --inst_subs_given                       false
% 4.17/1.00  --inst_orphan_elimination               true
% 4.17/1.00  --inst_learning_loop_flag               true
% 4.17/1.00  --inst_learning_start                   3000
% 4.17/1.00  --inst_learning_factor                  2
% 4.17/1.00  --inst_start_prop_sim_after_learn       3
% 4.17/1.00  --inst_sel_renew                        solver
% 4.17/1.00  --inst_lit_activity_flag                true
% 4.17/1.00  --inst_restr_to_given                   false
% 4.17/1.00  --inst_activity_threshold               500
% 4.17/1.00  --inst_out_proof                        true
% 4.17/1.00  
% 4.17/1.00  ------ Resolution Options
% 4.17/1.00  
% 4.17/1.00  --resolution_flag                       true
% 4.17/1.00  --res_lit_sel                           adaptive
% 4.17/1.00  --res_lit_sel_side                      none
% 4.17/1.00  --res_ordering                          kbo
% 4.17/1.00  --res_to_prop_solver                    active
% 4.17/1.00  --res_prop_simpl_new                    false
% 4.17/1.00  --res_prop_simpl_given                  true
% 4.17/1.00  --res_passive_queue_type                priority_queues
% 4.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.17/1.00  --res_passive_queues_freq               [15;5]
% 4.17/1.00  --res_forward_subs                      full
% 4.17/1.00  --res_backward_subs                     full
% 4.17/1.00  --res_forward_subs_resolution           true
% 4.17/1.00  --res_backward_subs_resolution          true
% 4.17/1.00  --res_orphan_elimination                true
% 4.17/1.00  --res_time_limit                        2.
% 4.17/1.00  --res_out_proof                         true
% 4.17/1.00  
% 4.17/1.00  ------ Superposition Options
% 4.17/1.00  
% 4.17/1.00  --superposition_flag                    true
% 4.17/1.00  --sup_passive_queue_type                priority_queues
% 4.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.17/1.00  --demod_completeness_check              fast
% 4.17/1.00  --demod_use_ground                      true
% 4.17/1.00  --sup_to_prop_solver                    passive
% 4.17/1.00  --sup_prop_simpl_new                    true
% 4.17/1.00  --sup_prop_simpl_given                  true
% 4.17/1.00  --sup_fun_splitting                     true
% 4.17/1.00  --sup_smt_interval                      50000
% 4.17/1.00  
% 4.17/1.00  ------ Superposition Simplification Setup
% 4.17/1.00  
% 4.17/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.17/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.17/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.17/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.17/1.00  --sup_immed_triv                        [TrivRules]
% 4.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_immed_bw_main                     []
% 4.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_input_bw                          []
% 4.17/1.00  
% 4.17/1.00  ------ Combination Options
% 4.17/1.00  
% 4.17/1.00  --comb_res_mult                         3
% 4.17/1.00  --comb_sup_mult                         2
% 4.17/1.00  --comb_inst_mult                        10
% 4.17/1.00  
% 4.17/1.00  ------ Debug Options
% 4.17/1.00  
% 4.17/1.00  --dbg_backtrace                         false
% 4.17/1.00  --dbg_dump_prop_clauses                 false
% 4.17/1.00  --dbg_dump_prop_clauses_file            -
% 4.17/1.00  --dbg_out_stat                          false
% 4.17/1.00  ------ Parsing...
% 4.17/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.17/1.00  ------ Proving...
% 4.17/1.00  ------ Problem Properties 
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  clauses                                 22
% 4.17/1.00  conjectures                             2
% 4.17/1.00  EPR                                     4
% 4.17/1.00  Horn                                    17
% 4.17/1.00  unary                                   7
% 4.17/1.00  binary                                  8
% 4.17/1.00  lits                                    45
% 4.17/1.00  lits eq                                 9
% 4.17/1.00  fd_pure                                 0
% 4.17/1.00  fd_pseudo                               0
% 4.17/1.00  fd_cond                                 0
% 4.17/1.00  fd_pseudo_cond                          4
% 4.17/1.00  AC symbols                              0
% 4.17/1.00  
% 4.17/1.00  ------ Schedule dynamic 5 is on 
% 4.17/1.00  
% 4.17/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  ------ 
% 4.17/1.00  Current options:
% 4.17/1.00  ------ 
% 4.17/1.00  
% 4.17/1.00  ------ Input Options
% 4.17/1.00  
% 4.17/1.00  --out_options                           all
% 4.17/1.00  --tptp_safe_out                         true
% 4.17/1.00  --problem_path                          ""
% 4.17/1.00  --include_path                          ""
% 4.17/1.00  --clausifier                            res/vclausify_rel
% 4.17/1.00  --clausifier_options                    ""
% 4.17/1.00  --stdin                                 false
% 4.17/1.00  --stats_out                             all
% 4.17/1.00  
% 4.17/1.00  ------ General Options
% 4.17/1.00  
% 4.17/1.00  --fof                                   false
% 4.17/1.00  --time_out_real                         305.
% 4.17/1.00  --time_out_virtual                      -1.
% 4.17/1.00  --symbol_type_check                     false
% 4.17/1.00  --clausify_out                          false
% 4.17/1.00  --sig_cnt_out                           false
% 4.17/1.00  --trig_cnt_out                          false
% 4.17/1.00  --trig_cnt_out_tolerance                1.
% 4.17/1.00  --trig_cnt_out_sk_spl                   false
% 4.17/1.00  --abstr_cl_out                          false
% 4.17/1.00  
% 4.17/1.00  ------ Global Options
% 4.17/1.00  
% 4.17/1.00  --schedule                              default
% 4.17/1.00  --add_important_lit                     false
% 4.17/1.00  --prop_solver_per_cl                    1000
% 4.17/1.00  --min_unsat_core                        false
% 4.17/1.00  --soft_assumptions                      false
% 4.17/1.00  --soft_lemma_size                       3
% 4.17/1.00  --prop_impl_unit_size                   0
% 4.17/1.00  --prop_impl_unit                        []
% 4.17/1.00  --share_sel_clauses                     true
% 4.17/1.00  --reset_solvers                         false
% 4.17/1.00  --bc_imp_inh                            [conj_cone]
% 4.17/1.00  --conj_cone_tolerance                   3.
% 4.17/1.00  --extra_neg_conj                        none
% 4.17/1.00  --large_theory_mode                     true
% 4.17/1.00  --prolific_symb_bound                   200
% 4.17/1.00  --lt_threshold                          2000
% 4.17/1.00  --clause_weak_htbl                      true
% 4.17/1.00  --gc_record_bc_elim                     false
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing Options
% 4.17/1.00  
% 4.17/1.00  --preprocessing_flag                    true
% 4.17/1.00  --time_out_prep_mult                    0.1
% 4.17/1.00  --splitting_mode                        input
% 4.17/1.00  --splitting_grd                         true
% 4.17/1.00  --splitting_cvd                         false
% 4.17/1.00  --splitting_cvd_svl                     false
% 4.17/1.00  --splitting_nvd                         32
% 4.17/1.00  --sub_typing                            true
% 4.17/1.00  --prep_gs_sim                           true
% 4.17/1.00  --prep_unflatten                        true
% 4.17/1.00  --prep_res_sim                          true
% 4.17/1.00  --prep_upred                            true
% 4.17/1.00  --prep_sem_filter                       exhaustive
% 4.17/1.00  --prep_sem_filter_out                   false
% 4.17/1.00  --pred_elim                             true
% 4.17/1.00  --res_sim_input                         true
% 4.17/1.00  --eq_ax_congr_red                       true
% 4.17/1.00  --pure_diseq_elim                       true
% 4.17/1.00  --brand_transform                       false
% 4.17/1.00  --non_eq_to_eq                          false
% 4.17/1.00  --prep_def_merge                        true
% 4.17/1.00  --prep_def_merge_prop_impl              false
% 4.17/1.00  --prep_def_merge_mbd                    true
% 4.17/1.00  --prep_def_merge_tr_red                 false
% 4.17/1.00  --prep_def_merge_tr_cl                  false
% 4.17/1.00  --smt_preprocessing                     true
% 4.17/1.00  --smt_ac_axioms                         fast
% 4.17/1.00  --preprocessed_out                      false
% 4.17/1.00  --preprocessed_stats                    false
% 4.17/1.00  
% 4.17/1.00  ------ Abstraction refinement Options
% 4.17/1.00  
% 4.17/1.00  --abstr_ref                             []
% 4.17/1.00  --abstr_ref_prep                        false
% 4.17/1.00  --abstr_ref_until_sat                   false
% 4.17/1.00  --abstr_ref_sig_restrict                funpre
% 4.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.17/1.00  --abstr_ref_under                       []
% 4.17/1.00  
% 4.17/1.00  ------ SAT Options
% 4.17/1.00  
% 4.17/1.00  --sat_mode                              false
% 4.17/1.00  --sat_fm_restart_options                ""
% 4.17/1.00  --sat_gr_def                            false
% 4.17/1.00  --sat_epr_types                         true
% 4.17/1.00  --sat_non_cyclic_types                  false
% 4.17/1.00  --sat_finite_models                     false
% 4.17/1.00  --sat_fm_lemmas                         false
% 4.17/1.00  --sat_fm_prep                           false
% 4.17/1.00  --sat_fm_uc_incr                        true
% 4.17/1.00  --sat_out_model                         small
% 4.17/1.00  --sat_out_clauses                       false
% 4.17/1.00  
% 4.17/1.00  ------ QBF Options
% 4.17/1.00  
% 4.17/1.00  --qbf_mode                              false
% 4.17/1.00  --qbf_elim_univ                         false
% 4.17/1.00  --qbf_dom_inst                          none
% 4.17/1.00  --qbf_dom_pre_inst                      false
% 4.17/1.00  --qbf_sk_in                             false
% 4.17/1.00  --qbf_pred_elim                         true
% 4.17/1.00  --qbf_split                             512
% 4.17/1.00  
% 4.17/1.00  ------ BMC1 Options
% 4.17/1.00  
% 4.17/1.00  --bmc1_incremental                      false
% 4.17/1.00  --bmc1_axioms                           reachable_all
% 4.17/1.00  --bmc1_min_bound                        0
% 4.17/1.00  --bmc1_max_bound                        -1
% 4.17/1.00  --bmc1_max_bound_default                -1
% 4.17/1.00  --bmc1_symbol_reachability              true
% 4.17/1.00  --bmc1_property_lemmas                  false
% 4.17/1.00  --bmc1_k_induction                      false
% 4.17/1.00  --bmc1_non_equiv_states                 false
% 4.17/1.00  --bmc1_deadlock                         false
% 4.17/1.00  --bmc1_ucm                              false
% 4.17/1.00  --bmc1_add_unsat_core                   none
% 4.17/1.00  --bmc1_unsat_core_children              false
% 4.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.17/1.00  --bmc1_out_stat                         full
% 4.17/1.00  --bmc1_ground_init                      false
% 4.17/1.00  --bmc1_pre_inst_next_state              false
% 4.17/1.00  --bmc1_pre_inst_state                   false
% 4.17/1.00  --bmc1_pre_inst_reach_state             false
% 4.17/1.00  --bmc1_out_unsat_core                   false
% 4.17/1.00  --bmc1_aig_witness_out                  false
% 4.17/1.00  --bmc1_verbose                          false
% 4.17/1.00  --bmc1_dump_clauses_tptp                false
% 4.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.17/1.00  --bmc1_dump_file                        -
% 4.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.17/1.00  --bmc1_ucm_extend_mode                  1
% 4.17/1.00  --bmc1_ucm_init_mode                    2
% 4.17/1.00  --bmc1_ucm_cone_mode                    none
% 4.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.17/1.00  --bmc1_ucm_relax_model                  4
% 4.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.17/1.00  --bmc1_ucm_layered_model                none
% 4.17/1.00  --bmc1_ucm_max_lemma_size               10
% 4.17/1.00  
% 4.17/1.00  ------ AIG Options
% 4.17/1.00  
% 4.17/1.00  --aig_mode                              false
% 4.17/1.00  
% 4.17/1.00  ------ Instantiation Options
% 4.17/1.00  
% 4.17/1.00  --instantiation_flag                    true
% 4.17/1.00  --inst_sos_flag                         true
% 4.17/1.00  --inst_sos_phase                        true
% 4.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.17/1.00  --inst_lit_sel_side                     none
% 4.17/1.00  --inst_solver_per_active                1400
% 4.17/1.00  --inst_solver_calls_frac                1.
% 4.17/1.00  --inst_passive_queue_type               priority_queues
% 4.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.17/1.00  --inst_passive_queues_freq              [25;2]
% 4.17/1.00  --inst_dismatching                      true
% 4.17/1.00  --inst_eager_unprocessed_to_passive     true
% 4.17/1.00  --inst_prop_sim_given                   true
% 4.17/1.00  --inst_prop_sim_new                     false
% 4.17/1.00  --inst_subs_new                         false
% 4.17/1.00  --inst_eq_res_simp                      false
% 4.17/1.00  --inst_subs_given                       false
% 4.17/1.00  --inst_orphan_elimination               true
% 4.17/1.00  --inst_learning_loop_flag               true
% 4.17/1.00  --inst_learning_start                   3000
% 4.17/1.00  --inst_learning_factor                  2
% 4.17/1.00  --inst_start_prop_sim_after_learn       3
% 4.17/1.00  --inst_sel_renew                        solver
% 4.17/1.00  --inst_lit_activity_flag                true
% 4.17/1.00  --inst_restr_to_given                   false
% 4.17/1.00  --inst_activity_threshold               500
% 4.17/1.00  --inst_out_proof                        true
% 4.17/1.00  
% 4.17/1.00  ------ Resolution Options
% 4.17/1.00  
% 4.17/1.00  --resolution_flag                       false
% 4.17/1.00  --res_lit_sel                           adaptive
% 4.17/1.00  --res_lit_sel_side                      none
% 4.17/1.00  --res_ordering                          kbo
% 4.17/1.00  --res_to_prop_solver                    active
% 4.17/1.00  --res_prop_simpl_new                    false
% 4.17/1.00  --res_prop_simpl_given                  true
% 4.17/1.00  --res_passive_queue_type                priority_queues
% 4.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.17/1.00  --res_passive_queues_freq               [15;5]
% 4.17/1.00  --res_forward_subs                      full
% 4.17/1.00  --res_backward_subs                     full
% 4.17/1.00  --res_forward_subs_resolution           true
% 4.17/1.00  --res_backward_subs_resolution          true
% 4.17/1.00  --res_orphan_elimination                true
% 4.17/1.00  --res_time_limit                        2.
% 4.17/1.00  --res_out_proof                         true
% 4.17/1.00  
% 4.17/1.00  ------ Superposition Options
% 4.17/1.00  
% 4.17/1.00  --superposition_flag                    true
% 4.17/1.00  --sup_passive_queue_type                priority_queues
% 4.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.17/1.00  --demod_completeness_check              fast
% 4.17/1.00  --demod_use_ground                      true
% 4.17/1.00  --sup_to_prop_solver                    passive
% 4.17/1.00  --sup_prop_simpl_new                    true
% 4.17/1.00  --sup_prop_simpl_given                  true
% 4.17/1.00  --sup_fun_splitting                     true
% 4.17/1.00  --sup_smt_interval                      50000
% 4.17/1.00  
% 4.17/1.00  ------ Superposition Simplification Setup
% 4.17/1.00  
% 4.17/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.17/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.17/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.17/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.17/1.00  --sup_immed_triv                        [TrivRules]
% 4.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_immed_bw_main                     []
% 4.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_input_bw                          []
% 4.17/1.00  
% 4.17/1.00  ------ Combination Options
% 4.17/1.00  
% 4.17/1.00  --comb_res_mult                         3
% 4.17/1.00  --comb_sup_mult                         2
% 4.17/1.00  --comb_inst_mult                        10
% 4.17/1.00  
% 4.17/1.00  ------ Debug Options
% 4.17/1.00  
% 4.17/1.00  --dbg_backtrace                         false
% 4.17/1.00  --dbg_dump_prop_clauses                 false
% 4.17/1.00  --dbg_dump_prop_clauses_file            -
% 4.17/1.00  --dbg_out_stat                          false
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  ------ Proving...
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  % SZS status Theorem for theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  fof(f17,conjecture,(
% 4.17/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f18,negated_conjecture,(
% 4.17/1.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 4.17/1.00    inference(negated_conjecture,[],[f17])).
% 4.17/1.00  
% 4.17/1.00  fof(f23,plain,(
% 4.17/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 4.17/1.00    inference(ennf_transformation,[],[f18])).
% 4.17/1.00  
% 4.17/1.00  fof(f39,plain,(
% 4.17/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4))),
% 4.17/1.00    introduced(choice_axiom,[])).
% 4.17/1.00  
% 4.17/1.00  fof(f40,plain,(
% 4.17/1.00    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4)),
% 4.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f39])).
% 4.17/1.00  
% 4.17/1.00  fof(f69,plain,(
% 4.17/1.00    r2_hidden(sK3,sK4)),
% 4.17/1.00    inference(cnf_transformation,[],[f40])).
% 4.17/1.00  
% 4.17/1.00  fof(f16,axiom,(
% 4.17/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f37,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.17/1.00    inference(nnf_transformation,[],[f16])).
% 4.17/1.00  
% 4.17/1.00  fof(f38,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.17/1.00    inference(flattening,[],[f37])).
% 4.17/1.00  
% 4.17/1.00  fof(f68,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f38])).
% 4.17/1.00  
% 4.17/1.00  fof(f12,axiom,(
% 4.17/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f62,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f12])).
% 4.17/1.00  
% 4.17/1.00  fof(f13,axiom,(
% 4.17/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f63,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f13])).
% 4.17/1.00  
% 4.17/1.00  fof(f14,axiom,(
% 4.17/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f64,plain,(
% 4.17/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f14])).
% 4.17/1.00  
% 4.17/1.00  fof(f71,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f63,f64])).
% 4.17/1.00  
% 4.17/1.00  fof(f72,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f62,f71])).
% 4.17/1.00  
% 4.17/1.00  fof(f84,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f68,f72])).
% 4.17/1.00  
% 4.17/1.00  fof(f7,axiom,(
% 4.17/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f22,plain,(
% 4.17/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.17/1.00    inference(ennf_transformation,[],[f7])).
% 4.17/1.00  
% 4.17/1.00  fof(f57,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f22])).
% 4.17/1.00  
% 4.17/1.00  fof(f8,axiom,(
% 4.17/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f58,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f8])).
% 4.17/1.00  
% 4.17/1.00  fof(f15,axiom,(
% 4.17/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f65,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f15])).
% 4.17/1.00  
% 4.17/1.00  fof(f73,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.17/1.00    inference(definition_unfolding,[],[f65,f72])).
% 4.17/1.00  
% 4.17/1.00  fof(f5,axiom,(
% 4.17/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f55,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f5])).
% 4.17/1.00  
% 4.17/1.00  fof(f82,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 4.17/1.00    inference(definition_unfolding,[],[f58,f73,f73,f55])).
% 4.17/1.00  
% 4.17/1.00  fof(f6,axiom,(
% 4.17/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f56,plain,(
% 4.17/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.17/1.00    inference(cnf_transformation,[],[f6])).
% 4.17/1.00  
% 4.17/1.00  fof(f81,plain,(
% 4.17/1.00    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 4.17/1.00    inference(definition_unfolding,[],[f56,f73])).
% 4.17/1.00  
% 4.17/1.00  fof(f2,axiom,(
% 4.17/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f28,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.17/1.00    inference(nnf_transformation,[],[f2])).
% 4.17/1.00  
% 4.17/1.00  fof(f29,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.17/1.00    inference(flattening,[],[f28])).
% 4.17/1.00  
% 4.17/1.00  fof(f30,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.17/1.00    inference(rectify,[],[f29])).
% 4.17/1.00  
% 4.17/1.00  fof(f31,plain,(
% 4.17/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.17/1.00    introduced(choice_axiom,[])).
% 4.17/1.00  
% 4.17/1.00  fof(f32,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 4.17/1.00  
% 4.17/1.00  fof(f47,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f32])).
% 4.17/1.00  
% 4.17/1.00  fof(f77,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f47,f55])).
% 4.17/1.00  
% 4.17/1.00  fof(f4,axiom,(
% 4.17/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f35,plain,(
% 4.17/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.17/1.00    inference(nnf_transformation,[],[f4])).
% 4.17/1.00  
% 4.17/1.00  fof(f36,plain,(
% 4.17/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.17/1.00    inference(flattening,[],[f35])).
% 4.17/1.00  
% 4.17/1.00  fof(f52,plain,(
% 4.17/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.17/1.00    inference(cnf_transformation,[],[f36])).
% 4.17/1.00  
% 4.17/1.00  fof(f92,plain,(
% 4.17/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.17/1.00    inference(equality_resolution,[],[f52])).
% 4.17/1.00  
% 4.17/1.00  fof(f44,plain,(
% 4.17/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.17/1.00    inference(cnf_transformation,[],[f32])).
% 4.17/1.00  
% 4.17/1.00  fof(f80,plain,(
% 4.17/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 4.17/1.00    inference(definition_unfolding,[],[f44,f55])).
% 4.17/1.00  
% 4.17/1.00  fof(f90,plain,(
% 4.17/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 4.17/1.00    inference(equality_resolution,[],[f80])).
% 4.17/1.00  
% 4.17/1.00  fof(f45,plain,(
% 4.17/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.17/1.00    inference(cnf_transformation,[],[f32])).
% 4.17/1.00  
% 4.17/1.00  fof(f79,plain,(
% 4.17/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 4.17/1.00    inference(definition_unfolding,[],[f45,f55])).
% 4.17/1.00  
% 4.17/1.00  fof(f89,plain,(
% 4.17/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 4.17/1.00    inference(equality_resolution,[],[f79])).
% 4.17/1.00  
% 4.17/1.00  fof(f1,axiom,(
% 4.17/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f20,plain,(
% 4.17/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.17/1.00    inference(ennf_transformation,[],[f1])).
% 4.17/1.00  
% 4.17/1.00  fof(f24,plain,(
% 4.17/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.17/1.00    inference(nnf_transformation,[],[f20])).
% 4.17/1.00  
% 4.17/1.00  fof(f25,plain,(
% 4.17/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.17/1.00    inference(rectify,[],[f24])).
% 4.17/1.00  
% 4.17/1.00  fof(f26,plain,(
% 4.17/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.17/1.00    introduced(choice_axiom,[])).
% 4.17/1.00  
% 4.17/1.00  fof(f27,plain,(
% 4.17/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 4.17/1.00  
% 4.17/1.00  fof(f42,plain,(
% 4.17/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f27])).
% 4.17/1.00  
% 4.17/1.00  fof(f3,axiom,(
% 4.17/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f19,plain,(
% 4.17/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.17/1.00    inference(rectify,[],[f3])).
% 4.17/1.00  
% 4.17/1.00  fof(f21,plain,(
% 4.17/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.17/1.00    inference(ennf_transformation,[],[f19])).
% 4.17/1.00  
% 4.17/1.00  fof(f33,plain,(
% 4.17/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 4.17/1.00    introduced(choice_axiom,[])).
% 4.17/1.00  
% 4.17/1.00  fof(f34,plain,(
% 4.17/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).
% 4.17/1.00  
% 4.17/1.00  fof(f50,plain,(
% 4.17/1.00    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f34])).
% 4.17/1.00  
% 4.17/1.00  fof(f51,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f34])).
% 4.17/1.00  
% 4.17/1.00  fof(f9,axiom,(
% 4.17/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f59,plain,(
% 4.17/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f9])).
% 4.17/1.00  
% 4.17/1.00  fof(f10,axiom,(
% 4.17/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f60,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f10])).
% 4.17/1.00  
% 4.17/1.00  fof(f83,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f60,f72,f72])).
% 4.17/1.00  
% 4.17/1.00  fof(f70,plain,(
% 4.17/1.00    k2_xboole_0(k1_tarski(sK3),sK4) != sK4),
% 4.17/1.00    inference(cnf_transformation,[],[f40])).
% 4.17/1.00  
% 4.17/1.00  fof(f11,axiom,(
% 4.17/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f61,plain,(
% 4.17/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f11])).
% 4.17/1.00  
% 4.17/1.00  fof(f74,plain,(
% 4.17/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f61,f72])).
% 4.17/1.00  
% 4.17/1.00  fof(f87,plain,(
% 4.17/1.00    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4),
% 4.17/1.00    inference(definition_unfolding,[],[f70,f73,f74])).
% 4.17/1.00  
% 4.17/1.00  cnf(c_23,negated_conjecture,
% 4.17/1.00      ( r2_hidden(sK3,sK4) ),
% 4.17/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_666,plain,
% 4.17/1.00      ( r2_hidden(sK3,sK4) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_19,plain,
% 4.17/1.00      ( ~ r2_hidden(X0,X1)
% 4.17/1.00      | ~ r2_hidden(X2,X1)
% 4.17/1.00      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 4.17/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_669,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.17/1.00      | r2_hidden(X2,X1) != iProver_top
% 4.17/1.00      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_15,plain,
% 4.17/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 4.17/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_670,plain,
% 4.17/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2657,plain,
% 4.17/1.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 4.17/1.00      | r2_hidden(X1,X2) != iProver_top
% 4.17/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_669,c_670]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_11369,plain,
% 4.17/1.00      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,X0),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,X0)
% 4.17/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_666,c_2657]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_11659,plain,
% 4.17/1.00      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_666,c_11369]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_16,plain,
% 4.17/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_11782,plain,
% 4.17/1.00      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_11659,c_16]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_14,plain,
% 4.17/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 4.17/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5,plain,
% 4.17/1.00      ( r2_hidden(sK1(X0,X1,X2),X0)
% 4.17/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 4.17/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 4.17/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_676,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 4.17/1.00      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 4.17/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_13,plain,
% 4.17/1.00      ( r1_tarski(X0,X0) ),
% 4.17/1.00      inference(cnf_transformation,[],[f92]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_671,plain,
% 4.17/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1020,plain,
% 4.17/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_671,c_670]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_8,plain,
% 4.17/1.00      ( r2_hidden(X0,X1)
% 4.17/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 4.17/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_673,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.17/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2033,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.17/1.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1020,c_673]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7,plain,
% 4.17/1.00      ( ~ r2_hidden(X0,X1)
% 4.17/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 4.17/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_674,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.17/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2669,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.17/1.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1020,c_674]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5507,plain,
% 4.17/1.00      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 4.17/1.00      inference(global_propositional_subsumption,
% 4.17/1.00                [status(thm)],
% 4.17/1.00                [c_2033,c_2669]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5515,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,X2)
% 4.17/1.00      | r2_hidden(sK1(X0,X1,k5_xboole_0(X2,X2)),X0) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_676,c_5507]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_10356,plain,
% 4.17/1.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X2,X2) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_5515,c_5507]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1,plain,
% 4.17/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 4.17/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_680,plain,
% 4.17/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.17/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_10,plain,
% 4.17/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f50]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_9,plain,
% 4.17/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_223,plain,
% 4.17/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 4.17/1.00      | r2_hidden(sK2(X1,X2),k3_xboole_0(X1,X2)) ),
% 4.17/1.00      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_665,plain,
% 4.17/1.00      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 4.17/1.00      | r2_hidden(sK2(X1,X2),k3_xboole_0(X1,X2)) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1299,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.17/1.00      | r2_hidden(sK2(X1,X1),k3_xboole_0(X1,X1)) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1020,c_665]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1300,plain,
% 4.17/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.17/1.00      | r2_hidden(sK2(X1,X1),X1) = iProver_top ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_1299,c_1020]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2509,plain,
% 4.17/1.00      ( r2_hidden(sK2(X0,X0),X0) = iProver_top
% 4.17/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_680,c_1300]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4400,plain,
% 4.17/1.00      ( k3_xboole_0(X0,X1) = X0
% 4.17/1.00      | r2_hidden(sK2(X0,X0),X0) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_2509,c_670]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5516,plain,
% 4.17/1.00      ( k3_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(X0,X0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_4400,c_5507]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_17,plain,
% 4.17/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 4.17/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_234,plain,
% 4.17/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 4.17/1.00      | X3 != X1
% 4.17/1.00      | k1_xboole_0 != X2 ),
% 4.17/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_235,plain,
% 4.17/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 4.17/1.00      inference(unflattening,[status(thm)],[c_234]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_664,plain,
% 4.17/1.00      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1141,plain,
% 4.17/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1020,c_664]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_3875,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 4.17/1.00      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_676,c_1141]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5555,plain,
% 4.17/1.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k1_xboole_0 ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_3875,c_5507]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5556,plain,
% 4.17/1.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k1_xboole_0 ),
% 4.17/1.00      inference(light_normalisation,[status(thm)],[c_5555,c_5516]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_10357,plain,
% 4.17/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.17/1.00      inference(light_normalisation,
% 4.17/1.00                [status(thm)],
% 4.17/1.00                [c_10356,c_5516,c_5556]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_11788,plain,
% 4.17/1.00      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_11782,c_14,c_10357]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_18,plain,
% 4.17/1.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 4.17/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_22,negated_conjecture,
% 4.17/1.00      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
% 4.17/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1304,plain,
% 4.17/1.00      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_18,c_22]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(contradiction,plain,
% 4.17/1.00      ( $false ),
% 4.17/1.00      inference(minisat,[status(thm)],[c_11788,c_1304]) ).
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  ------                               Statistics
% 4.17/1.00  
% 4.17/1.00  ------ General
% 4.17/1.00  
% 4.17/1.00  abstr_ref_over_cycles:                  0
% 4.17/1.00  abstr_ref_under_cycles:                 0
% 4.17/1.00  gc_basic_clause_elim:                   0
% 4.17/1.00  forced_gc_time:                         0
% 4.17/1.00  parsing_time:                           0.008
% 4.17/1.00  unif_index_cands_time:                  0.
% 4.17/1.00  unif_index_add_time:                    0.
% 4.17/1.00  orderings_time:                         0.
% 4.17/1.00  out_proof_time:                         0.007
% 4.17/1.00  total_time:                             0.464
% 4.17/1.00  num_of_symbols:                         44
% 4.17/1.00  num_of_terms:                           13769
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing
% 4.17/1.00  
% 4.17/1.00  num_of_splits:                          0
% 4.17/1.00  num_of_split_atoms:                     0
% 4.17/1.00  num_of_reused_defs:                     0
% 4.17/1.00  num_eq_ax_congr_red:                    32
% 4.17/1.00  num_of_sem_filtered_clauses:            1
% 4.17/1.00  num_of_subtypes:                        0
% 4.17/1.00  monotx_restored_types:                  0
% 4.17/1.00  sat_num_of_epr_types:                   0
% 4.17/1.00  sat_num_of_non_cyclic_types:            0
% 4.17/1.00  sat_guarded_non_collapsed_types:        0
% 4.17/1.00  num_pure_diseq_elim:                    0
% 4.17/1.00  simp_replaced_by:                       0
% 4.17/1.00  res_preprocessed:                       106
% 4.17/1.00  prep_upred:                             0
% 4.17/1.00  prep_unflattend:                        2
% 4.17/1.00  smt_new_axioms:                         0
% 4.17/1.00  pred_elim_cands:                        2
% 4.17/1.00  pred_elim:                              1
% 4.17/1.00  pred_elim_cl:                           1
% 4.17/1.00  pred_elim_cycles:                       3
% 4.17/1.00  merged_defs:                            0
% 4.17/1.00  merged_defs_ncl:                        0
% 4.17/1.00  bin_hyper_res:                          0
% 4.17/1.00  prep_cycles:                            4
% 4.17/1.00  pred_elim_time:                         0.001
% 4.17/1.00  splitting_time:                         0.
% 4.17/1.00  sem_filter_time:                        0.
% 4.17/1.00  monotx_time:                            0.
% 4.17/1.00  subtype_inf_time:                       0.
% 4.17/1.00  
% 4.17/1.00  ------ Problem properties
% 4.17/1.00  
% 4.17/1.00  clauses:                                22
% 4.17/1.00  conjectures:                            2
% 4.17/1.00  epr:                                    4
% 4.17/1.00  horn:                                   17
% 4.17/1.00  ground:                                 2
% 4.17/1.00  unary:                                  7
% 4.17/1.00  binary:                                 8
% 4.17/1.00  lits:                                   45
% 4.17/1.00  lits_eq:                                9
% 4.17/1.00  fd_pure:                                0
% 4.17/1.00  fd_pseudo:                              0
% 4.17/1.00  fd_cond:                                0
% 4.17/1.00  fd_pseudo_cond:                         4
% 4.17/1.00  ac_symbols:                             0
% 4.17/1.00  
% 4.17/1.00  ------ Propositional Solver
% 4.17/1.00  
% 4.17/1.00  prop_solver_calls:                      30
% 4.17/1.00  prop_fast_solver_calls:                 697
% 4.17/1.00  smt_solver_calls:                       0
% 4.17/1.00  smt_fast_solver_calls:                  0
% 4.17/1.00  prop_num_of_clauses:                    4657
% 4.17/1.00  prop_preprocess_simplified:             10874
% 4.17/1.00  prop_fo_subsumed:                       4
% 4.17/1.00  prop_solver_time:                       0.
% 4.17/1.00  smt_solver_time:                        0.
% 4.17/1.00  smt_fast_solver_time:                   0.
% 4.17/1.00  prop_fast_solver_time:                  0.
% 4.17/1.00  prop_unsat_core_time:                   0.
% 4.17/1.00  
% 4.17/1.00  ------ QBF
% 4.17/1.00  
% 4.17/1.00  qbf_q_res:                              0
% 4.17/1.00  qbf_num_tautologies:                    0
% 4.17/1.00  qbf_prep_cycles:                        0
% 4.17/1.00  
% 4.17/1.00  ------ BMC1
% 4.17/1.00  
% 4.17/1.00  bmc1_current_bound:                     -1
% 4.17/1.00  bmc1_last_solved_bound:                 -1
% 4.17/1.00  bmc1_unsat_core_size:                   -1
% 4.17/1.00  bmc1_unsat_core_parents_size:           -1
% 4.17/1.00  bmc1_merge_next_fun:                    0
% 4.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.17/1.00  
% 4.17/1.00  ------ Instantiation
% 4.17/1.00  
% 4.17/1.00  inst_num_of_clauses:                    1122
% 4.17/1.00  inst_num_in_passive:                    375
% 4.17/1.00  inst_num_in_active:                     406
% 4.17/1.00  inst_num_in_unprocessed:                341
% 4.17/1.00  inst_num_of_loops:                      550
% 4.17/1.00  inst_num_of_learning_restarts:          0
% 4.17/1.00  inst_num_moves_active_passive:          143
% 4.17/1.00  inst_lit_activity:                      0
% 4.17/1.00  inst_lit_activity_moves:                0
% 4.17/1.00  inst_num_tautologies:                   0
% 4.17/1.00  inst_num_prop_implied:                  0
% 4.17/1.00  inst_num_existing_simplified:           0
% 4.17/1.00  inst_num_eq_res_simplified:             0
% 4.17/1.00  inst_num_child_elim:                    0
% 4.17/1.00  inst_num_of_dismatching_blockings:      1741
% 4.17/1.00  inst_num_of_non_proper_insts:           1521
% 4.17/1.00  inst_num_of_duplicates:                 0
% 4.17/1.00  inst_inst_num_from_inst_to_res:         0
% 4.17/1.00  inst_dismatching_checking_time:         0.
% 4.17/1.00  
% 4.17/1.00  ------ Resolution
% 4.17/1.00  
% 4.17/1.00  res_num_of_clauses:                     0
% 4.17/1.00  res_num_in_passive:                     0
% 4.17/1.00  res_num_in_active:                      0
% 4.17/1.00  res_num_of_loops:                       110
% 4.17/1.00  res_forward_subset_subsumed:            91
% 4.17/1.00  res_backward_subset_subsumed:           0
% 4.17/1.00  res_forward_subsumed:                   0
% 4.17/1.00  res_backward_subsumed:                  0
% 4.17/1.00  res_forward_subsumption_resolution:     0
% 4.17/1.00  res_backward_subsumption_resolution:    0
% 4.17/1.00  res_clause_to_clause_subsumption:       2084
% 4.17/1.00  res_orphan_elimination:                 0
% 4.17/1.00  res_tautology_del:                      89
% 4.17/1.00  res_num_eq_res_simplified:              0
% 4.17/1.00  res_num_sel_changes:                    0
% 4.17/1.00  res_moves_from_active_to_pass:          0
% 4.17/1.00  
% 4.17/1.00  ------ Superposition
% 4.17/1.00  
% 4.17/1.00  sup_time_total:                         0.
% 4.17/1.00  sup_time_generating:                    0.
% 4.17/1.00  sup_time_sim_full:                      0.
% 4.17/1.00  sup_time_sim_immed:                     0.
% 4.17/1.00  
% 4.17/1.00  sup_num_of_clauses:                     272
% 4.17/1.00  sup_num_in_active:                      102
% 4.17/1.00  sup_num_in_passive:                     170
% 4.17/1.00  sup_num_of_loops:                       109
% 4.17/1.00  sup_fw_superposition:                   519
% 4.17/1.00  sup_bw_superposition:                   348
% 4.17/1.00  sup_immediate_simplified:               382
% 4.17/1.00  sup_given_eliminated:                   1
% 4.17/1.00  comparisons_done:                       0
% 4.17/1.00  comparisons_avoided:                    0
% 4.17/1.00  
% 4.17/1.00  ------ Simplifications
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  sim_fw_subset_subsumed:                 45
% 4.17/1.00  sim_bw_subset_subsumed:                 2
% 4.17/1.00  sim_fw_subsumed:                        195
% 4.17/1.00  sim_bw_subsumed:                        4
% 4.17/1.00  sim_fw_subsumption_res:                 0
% 4.17/1.00  sim_bw_subsumption_res:                 0
% 4.17/1.00  sim_tautology_del:                      14
% 4.17/1.00  sim_eq_tautology_del:                   22
% 4.17/1.00  sim_eq_res_simp:                        1
% 4.17/1.00  sim_fw_demodulated:                     212
% 4.17/1.00  sim_bw_demodulated:                     8
% 4.17/1.00  sim_light_normalised:                   129
% 4.17/1.00  sim_joinable_taut:                      0
% 4.17/1.00  sim_joinable_simp:                      0
% 4.17/1.00  sim_ac_normalised:                      0
% 4.17/1.00  sim_smt_subsumption:                    0
% 4.17/1.00  
%------------------------------------------------------------------------------
