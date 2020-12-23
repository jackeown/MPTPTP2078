%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:54 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  110 (1001 expanded)
%              Number of clauses        :   43 ( 116 expanded)
%              Number of leaves         :   20 ( 341 expanded)
%              Depth                    :   18
%              Number of atoms          :  304 (1221 expanded)
%              Number of equality atoms :  237 (1142 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f71,f58])).

fof(f88,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f65,f72,f72])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f71,f58])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_enumset1(X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f57,f71,f58,f73])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK2 != sK4
      & sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( sK2 != sK4
    & sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f35])).

fof(f68,plain,(
    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK3,sK4)) ),
    inference(definition_unfolding,[],[f68,f58])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f67,f37,f58])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
    inference(definition_unfolding,[],[f66,f58,f58])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f94,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f95,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f94])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f70,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2121,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_21,c_19])).

cnf(c_2997,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_2121,c_19])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3103,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k3_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_2997,c_1])).

cnf(c_18,plain,
    ( k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_enumset1(X0,X1,X2,X3)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4695,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_3103,c_18])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2717,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_19,c_0])).

cnf(c_2996,plain,
    ( k2_enumset1(X0,X0,X1,X0) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_2121,c_0])).

cnf(c_3501,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X1,X0,X2),k3_xboole_0(k2_enumset1(X0,X1,X0,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_2996,c_18])).

cnf(c_3527,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X0,X2) ),
    inference(demodulation,[status(thm)],[c_3501,c_1])).

cnf(c_4700,plain,
    ( k2_enumset1(X0,X1,X0,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_4695,c_2717,c_3527])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_191,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k2_tarski(sK3,sK4) != X1
    | k2_tarski(sK2,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_192,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK4)) = k2_tarski(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_3761,plain,
    ( k5_xboole_0(k2_tarski(sK3,sK4),k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK2,sK2))) = k2_enumset1(sK3,sK4,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_192,c_3527])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,plain,
    ( k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2069,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23,c_22])).

cnf(c_3769,plain,
    ( k2_enumset1(sK3,sK4,sK3,sK2) = k2_tarski(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3761,c_3,c_2069])).

cnf(c_4036,plain,
    ( k5_xboole_0(k2_enumset1(X0,sK3,sK4,sK3),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_enumset1(X0,sK3,sK4,sK3)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k2_tarski(X0,X0)))) ),
    inference(superposition,[status(thm)],[c_3769,c_18])).

cnf(c_4044,plain,
    ( k5_xboole_0(k2_enumset1(X0,sK3,sK4,sK3),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_enumset1(X0,sK3,sK4,sK3)))) = k2_enumset1(X0,X0,sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_4036,c_2121])).

cnf(c_5173,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)))) = k2_enumset1(sK4,sK4,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_4700,c_4044])).

cnf(c_3512,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_18,c_1])).

cnf(c_3763,plain,
    ( k2_enumset1(X0,X0,X1,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3527,c_2121])).

cnf(c_3766,plain,
    ( k2_enumset1(X0,X0,X1,X1) = k2_tarski(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3763,c_2717])).

cnf(c_5225,plain,
    ( k2_enumset1(sK4,sK3,sK4,sK2) = k2_tarski(sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_5173,c_2717,c_3512,c_3527,c_3766])).

cnf(c_5341,plain,
    ( k2_enumset1(sK4,sK4,sK2,sK3) = k2_tarski(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_5225,c_4700])).

cnf(c_9,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2049,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2089,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19,c_2049])).

cnf(c_5373,plain,
    ( r2_hidden(sK2,k2_tarski(sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5341,c_2089])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2209,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK4,X0))
    | sK2 = X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2273,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK4,sK3))
    | sK2 = sK3
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_2274,plain,
    ( sK2 = sK3
    | sK2 = sK4
    | r2_hidden(sK2,k2_tarski(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2273])).

cnf(c_24,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5373,c_2274,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:12:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.50/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/1.00  
% 2.50/1.00  ------  iProver source info
% 2.50/1.00  
% 2.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/1.00  git: non_committed_changes: false
% 2.50/1.00  git: last_make_outside_of_git: false
% 2.50/1.00  
% 2.50/1.00  ------ 
% 2.50/1.00  
% 2.50/1.00  ------ Input Options
% 2.50/1.00  
% 2.50/1.00  --out_options                           all
% 2.50/1.00  --tptp_safe_out                         true
% 2.50/1.00  --problem_path                          ""
% 2.50/1.00  --include_path                          ""
% 2.50/1.00  --clausifier                            res/vclausify_rel
% 2.50/1.00  --clausifier_options                    --mode clausify
% 2.50/1.00  --stdin                                 false
% 2.50/1.00  --stats_out                             all
% 2.50/1.00  
% 2.50/1.00  ------ General Options
% 2.50/1.00  
% 2.50/1.00  --fof                                   false
% 2.50/1.00  --time_out_real                         305.
% 2.50/1.00  --time_out_virtual                      -1.
% 2.50/1.00  --symbol_type_check                     false
% 2.50/1.00  --clausify_out                          false
% 2.50/1.00  --sig_cnt_out                           false
% 2.50/1.00  --trig_cnt_out                          false
% 2.50/1.00  --trig_cnt_out_tolerance                1.
% 2.50/1.00  --trig_cnt_out_sk_spl                   false
% 2.50/1.00  --abstr_cl_out                          false
% 2.50/1.00  
% 2.50/1.00  ------ Global Options
% 2.50/1.00  
% 2.50/1.00  --schedule                              default
% 2.50/1.00  --add_important_lit                     false
% 2.50/1.00  --prop_solver_per_cl                    1000
% 2.50/1.00  --min_unsat_core                        false
% 2.50/1.00  --soft_assumptions                      false
% 2.50/1.00  --soft_lemma_size                       3
% 2.50/1.00  --prop_impl_unit_size                   0
% 2.50/1.00  --prop_impl_unit                        []
% 2.50/1.00  --share_sel_clauses                     true
% 2.50/1.00  --reset_solvers                         false
% 2.50/1.00  --bc_imp_inh                            [conj_cone]
% 2.50/1.00  --conj_cone_tolerance                   3.
% 2.50/1.00  --extra_neg_conj                        none
% 2.50/1.00  --large_theory_mode                     true
% 2.50/1.00  --prolific_symb_bound                   200
% 2.50/1.00  --lt_threshold                          2000
% 2.50/1.00  --clause_weak_htbl                      true
% 2.50/1.00  --gc_record_bc_elim                     false
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing Options
% 2.50/1.00  
% 2.50/1.00  --preprocessing_flag                    true
% 2.50/1.00  --time_out_prep_mult                    0.1
% 2.50/1.00  --splitting_mode                        input
% 2.50/1.00  --splitting_grd                         true
% 2.50/1.00  --splitting_cvd                         false
% 2.50/1.00  --splitting_cvd_svl                     false
% 2.50/1.00  --splitting_nvd                         32
% 2.50/1.00  --sub_typing                            true
% 2.50/1.00  --prep_gs_sim                           true
% 2.50/1.00  --prep_unflatten                        true
% 2.50/1.00  --prep_res_sim                          true
% 2.50/1.00  --prep_upred                            true
% 2.50/1.00  --prep_sem_filter                       exhaustive
% 2.50/1.00  --prep_sem_filter_out                   false
% 2.50/1.00  --pred_elim                             true
% 2.50/1.00  --res_sim_input                         true
% 2.50/1.00  --eq_ax_congr_red                       true
% 2.50/1.00  --pure_diseq_elim                       true
% 2.50/1.00  --brand_transform                       false
% 2.50/1.00  --non_eq_to_eq                          false
% 2.50/1.00  --prep_def_merge                        true
% 2.50/1.00  --prep_def_merge_prop_impl              false
% 2.50/1.00  --prep_def_merge_mbd                    true
% 2.50/1.00  --prep_def_merge_tr_red                 false
% 2.50/1.00  --prep_def_merge_tr_cl                  false
% 2.50/1.00  --smt_preprocessing                     true
% 2.50/1.00  --smt_ac_axioms                         fast
% 2.50/1.00  --preprocessed_out                      false
% 2.50/1.00  --preprocessed_stats                    false
% 2.50/1.00  
% 2.50/1.00  ------ Abstraction refinement Options
% 2.50/1.00  
% 2.50/1.00  --abstr_ref                             []
% 2.50/1.00  --abstr_ref_prep                        false
% 2.50/1.00  --abstr_ref_until_sat                   false
% 2.50/1.00  --abstr_ref_sig_restrict                funpre
% 2.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/1.00  --abstr_ref_under                       []
% 2.50/1.00  
% 2.50/1.00  ------ SAT Options
% 2.50/1.00  
% 2.50/1.00  --sat_mode                              false
% 2.50/1.00  --sat_fm_restart_options                ""
% 2.50/1.00  --sat_gr_def                            false
% 2.50/1.00  --sat_epr_types                         true
% 2.50/1.00  --sat_non_cyclic_types                  false
% 2.50/1.00  --sat_finite_models                     false
% 2.50/1.00  --sat_fm_lemmas                         false
% 2.50/1.00  --sat_fm_prep                           false
% 2.50/1.00  --sat_fm_uc_incr                        true
% 2.50/1.00  --sat_out_model                         small
% 2.50/1.00  --sat_out_clauses                       false
% 2.50/1.00  
% 2.50/1.00  ------ QBF Options
% 2.50/1.00  
% 2.50/1.00  --qbf_mode                              false
% 2.50/1.00  --qbf_elim_univ                         false
% 2.50/1.00  --qbf_dom_inst                          none
% 2.50/1.00  --qbf_dom_pre_inst                      false
% 2.50/1.00  --qbf_sk_in                             false
% 2.50/1.00  --qbf_pred_elim                         true
% 2.50/1.00  --qbf_split                             512
% 2.50/1.00  
% 2.50/1.00  ------ BMC1 Options
% 2.50/1.00  
% 2.50/1.00  --bmc1_incremental                      false
% 2.50/1.00  --bmc1_axioms                           reachable_all
% 2.50/1.00  --bmc1_min_bound                        0
% 2.50/1.00  --bmc1_max_bound                        -1
% 2.50/1.00  --bmc1_max_bound_default                -1
% 2.50/1.00  --bmc1_symbol_reachability              true
% 2.50/1.00  --bmc1_property_lemmas                  false
% 2.50/1.00  --bmc1_k_induction                      false
% 2.50/1.00  --bmc1_non_equiv_states                 false
% 2.50/1.00  --bmc1_deadlock                         false
% 2.50/1.00  --bmc1_ucm                              false
% 2.50/1.00  --bmc1_add_unsat_core                   none
% 2.50/1.00  --bmc1_unsat_core_children              false
% 2.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/1.00  --bmc1_out_stat                         full
% 2.50/1.00  --bmc1_ground_init                      false
% 2.50/1.00  --bmc1_pre_inst_next_state              false
% 2.50/1.00  --bmc1_pre_inst_state                   false
% 2.50/1.00  --bmc1_pre_inst_reach_state             false
% 2.50/1.00  --bmc1_out_unsat_core                   false
% 2.50/1.00  --bmc1_aig_witness_out                  false
% 2.50/1.00  --bmc1_verbose                          false
% 2.50/1.00  --bmc1_dump_clauses_tptp                false
% 2.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.50/1.00  --bmc1_dump_file                        -
% 2.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.50/1.00  --bmc1_ucm_extend_mode                  1
% 2.50/1.00  --bmc1_ucm_init_mode                    2
% 2.50/1.00  --bmc1_ucm_cone_mode                    none
% 2.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.50/1.00  --bmc1_ucm_relax_model                  4
% 2.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/1.00  --bmc1_ucm_layered_model                none
% 2.50/1.00  --bmc1_ucm_max_lemma_size               10
% 2.50/1.00  
% 2.50/1.00  ------ AIG Options
% 2.50/1.00  
% 2.50/1.00  --aig_mode                              false
% 2.50/1.00  
% 2.50/1.00  ------ Instantiation Options
% 2.50/1.00  
% 2.50/1.00  --instantiation_flag                    true
% 2.50/1.00  --inst_sos_flag                         false
% 2.50/1.00  --inst_sos_phase                        true
% 2.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel_side                     num_symb
% 2.50/1.00  --inst_solver_per_active                1400
% 2.50/1.00  --inst_solver_calls_frac                1.
% 2.50/1.00  --inst_passive_queue_type               priority_queues
% 2.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/1.00  --inst_passive_queues_freq              [25;2]
% 2.50/1.00  --inst_dismatching                      true
% 2.50/1.00  --inst_eager_unprocessed_to_passive     true
% 2.50/1.00  --inst_prop_sim_given                   true
% 2.50/1.00  --inst_prop_sim_new                     false
% 2.50/1.00  --inst_subs_new                         false
% 2.50/1.00  --inst_eq_res_simp                      false
% 2.50/1.00  --inst_subs_given                       false
% 2.50/1.00  --inst_orphan_elimination               true
% 2.50/1.00  --inst_learning_loop_flag               true
% 2.50/1.00  --inst_learning_start                   3000
% 2.50/1.00  --inst_learning_factor                  2
% 2.50/1.00  --inst_start_prop_sim_after_learn       3
% 2.50/1.00  --inst_sel_renew                        solver
% 2.50/1.00  --inst_lit_activity_flag                true
% 2.50/1.00  --inst_restr_to_given                   false
% 2.50/1.00  --inst_activity_threshold               500
% 2.50/1.00  --inst_out_proof                        true
% 2.50/1.00  
% 2.50/1.00  ------ Resolution Options
% 2.50/1.00  
% 2.50/1.00  --resolution_flag                       true
% 2.50/1.00  --res_lit_sel                           adaptive
% 2.50/1.00  --res_lit_sel_side                      none
% 2.50/1.00  --res_ordering                          kbo
% 2.50/1.00  --res_to_prop_solver                    active
% 2.50/1.00  --res_prop_simpl_new                    false
% 2.50/1.00  --res_prop_simpl_given                  true
% 2.50/1.00  --res_passive_queue_type                priority_queues
% 2.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/1.00  --res_passive_queues_freq               [15;5]
% 2.50/1.00  --res_forward_subs                      full
% 2.50/1.00  --res_backward_subs                     full
% 2.50/1.00  --res_forward_subs_resolution           true
% 2.50/1.00  --res_backward_subs_resolution          true
% 2.50/1.00  --res_orphan_elimination                true
% 2.50/1.00  --res_time_limit                        2.
% 2.50/1.00  --res_out_proof                         true
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Options
% 2.50/1.00  
% 2.50/1.00  --superposition_flag                    true
% 2.50/1.00  --sup_passive_queue_type                priority_queues
% 2.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.50/1.00  --demod_completeness_check              fast
% 2.50/1.00  --demod_use_ground                      true
% 2.50/1.00  --sup_to_prop_solver                    passive
% 2.50/1.00  --sup_prop_simpl_new                    true
% 2.50/1.00  --sup_prop_simpl_given                  true
% 2.50/1.00  --sup_fun_splitting                     false
% 2.50/1.00  --sup_smt_interval                      50000
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Simplification Setup
% 2.50/1.00  
% 2.50/1.00  --sup_indices_passive                   []
% 2.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_full_bw                           [BwDemod]
% 2.50/1.00  --sup_immed_triv                        [TrivRules]
% 2.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_immed_bw_main                     []
% 2.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  
% 2.50/1.00  ------ Combination Options
% 2.50/1.00  
% 2.50/1.00  --comb_res_mult                         3
% 2.50/1.00  --comb_sup_mult                         2
% 2.50/1.00  --comb_inst_mult                        10
% 2.50/1.00  
% 2.50/1.00  ------ Debug Options
% 2.50/1.00  
% 2.50/1.00  --dbg_backtrace                         false
% 2.50/1.00  --dbg_dump_prop_clauses                 false
% 2.50/1.00  --dbg_dump_prop_clauses_file            -
% 2.50/1.00  --dbg_out_stat                          false
% 2.50/1.00  ------ Parsing...
% 2.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/1.00  ------ Proving...
% 2.50/1.00  ------ Problem Properties 
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  clauses                                 26
% 2.50/1.00  conjectures                             2
% 2.50/1.00  EPR                                     2
% 2.50/1.00  Horn                                    22
% 2.50/1.00  unary                                   17
% 2.50/1.00  binary                                  0
% 2.50/1.00  lits                                    48
% 2.50/1.00  lits eq                                 34
% 2.50/1.00  fd_pure                                 0
% 2.50/1.00  fd_pseudo                               0
% 2.50/1.00  fd_cond                                 0
% 2.50/1.00  fd_pseudo_cond                          7
% 2.50/1.00  AC symbols                              0
% 2.50/1.00  
% 2.50/1.00  ------ Schedule dynamic 5 is on 
% 2.50/1.00  
% 2.50/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  ------ 
% 2.50/1.00  Current options:
% 2.50/1.00  ------ 
% 2.50/1.00  
% 2.50/1.00  ------ Input Options
% 2.50/1.00  
% 2.50/1.00  --out_options                           all
% 2.50/1.00  --tptp_safe_out                         true
% 2.50/1.00  --problem_path                          ""
% 2.50/1.00  --include_path                          ""
% 2.50/1.00  --clausifier                            res/vclausify_rel
% 2.50/1.00  --clausifier_options                    --mode clausify
% 2.50/1.00  --stdin                                 false
% 2.50/1.00  --stats_out                             all
% 2.50/1.00  
% 2.50/1.00  ------ General Options
% 2.50/1.00  
% 2.50/1.00  --fof                                   false
% 2.50/1.00  --time_out_real                         305.
% 2.50/1.00  --time_out_virtual                      -1.
% 2.50/1.00  --symbol_type_check                     false
% 2.50/1.00  --clausify_out                          false
% 2.50/1.00  --sig_cnt_out                           false
% 2.50/1.00  --trig_cnt_out                          false
% 2.50/1.00  --trig_cnt_out_tolerance                1.
% 2.50/1.00  --trig_cnt_out_sk_spl                   false
% 2.50/1.00  --abstr_cl_out                          false
% 2.50/1.00  
% 2.50/1.00  ------ Global Options
% 2.50/1.00  
% 2.50/1.00  --schedule                              default
% 2.50/1.00  --add_important_lit                     false
% 2.50/1.00  --prop_solver_per_cl                    1000
% 2.50/1.00  --min_unsat_core                        false
% 2.50/1.00  --soft_assumptions                      false
% 2.50/1.00  --soft_lemma_size                       3
% 2.50/1.00  --prop_impl_unit_size                   0
% 2.50/1.00  --prop_impl_unit                        []
% 2.50/1.00  --share_sel_clauses                     true
% 2.50/1.00  --reset_solvers                         false
% 2.50/1.00  --bc_imp_inh                            [conj_cone]
% 2.50/1.00  --conj_cone_tolerance                   3.
% 2.50/1.00  --extra_neg_conj                        none
% 2.50/1.00  --large_theory_mode                     true
% 2.50/1.00  --prolific_symb_bound                   200
% 2.50/1.00  --lt_threshold                          2000
% 2.50/1.00  --clause_weak_htbl                      true
% 2.50/1.00  --gc_record_bc_elim                     false
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing Options
% 2.50/1.00  
% 2.50/1.00  --preprocessing_flag                    true
% 2.50/1.00  --time_out_prep_mult                    0.1
% 2.50/1.00  --splitting_mode                        input
% 2.50/1.00  --splitting_grd                         true
% 2.50/1.00  --splitting_cvd                         false
% 2.50/1.00  --splitting_cvd_svl                     false
% 2.50/1.00  --splitting_nvd                         32
% 2.50/1.00  --sub_typing                            true
% 2.50/1.00  --prep_gs_sim                           true
% 2.50/1.00  --prep_unflatten                        true
% 2.50/1.00  --prep_res_sim                          true
% 2.50/1.00  --prep_upred                            true
% 2.50/1.00  --prep_sem_filter                       exhaustive
% 2.50/1.00  --prep_sem_filter_out                   false
% 2.50/1.00  --pred_elim                             true
% 2.50/1.00  --res_sim_input                         true
% 2.50/1.00  --eq_ax_congr_red                       true
% 2.50/1.00  --pure_diseq_elim                       true
% 2.50/1.00  --brand_transform                       false
% 2.50/1.00  --non_eq_to_eq                          false
% 2.50/1.00  --prep_def_merge                        true
% 2.50/1.00  --prep_def_merge_prop_impl              false
% 2.50/1.00  --prep_def_merge_mbd                    true
% 2.50/1.00  --prep_def_merge_tr_red                 false
% 2.50/1.00  --prep_def_merge_tr_cl                  false
% 2.50/1.00  --smt_preprocessing                     true
% 2.50/1.00  --smt_ac_axioms                         fast
% 2.50/1.00  --preprocessed_out                      false
% 2.50/1.00  --preprocessed_stats                    false
% 2.50/1.00  
% 2.50/1.00  ------ Abstraction refinement Options
% 2.50/1.00  
% 2.50/1.00  --abstr_ref                             []
% 2.50/1.00  --abstr_ref_prep                        false
% 2.50/1.00  --abstr_ref_until_sat                   false
% 2.50/1.00  --abstr_ref_sig_restrict                funpre
% 2.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/1.00  --abstr_ref_under                       []
% 2.50/1.00  
% 2.50/1.00  ------ SAT Options
% 2.50/1.00  
% 2.50/1.00  --sat_mode                              false
% 2.50/1.00  --sat_fm_restart_options                ""
% 2.50/1.00  --sat_gr_def                            false
% 2.50/1.00  --sat_epr_types                         true
% 2.50/1.00  --sat_non_cyclic_types                  false
% 2.50/1.00  --sat_finite_models                     false
% 2.50/1.00  --sat_fm_lemmas                         false
% 2.50/1.00  --sat_fm_prep                           false
% 2.50/1.00  --sat_fm_uc_incr                        true
% 2.50/1.00  --sat_out_model                         small
% 2.50/1.00  --sat_out_clauses                       false
% 2.50/1.00  
% 2.50/1.00  ------ QBF Options
% 2.50/1.00  
% 2.50/1.00  --qbf_mode                              false
% 2.50/1.00  --qbf_elim_univ                         false
% 2.50/1.00  --qbf_dom_inst                          none
% 2.50/1.00  --qbf_dom_pre_inst                      false
% 2.50/1.00  --qbf_sk_in                             false
% 2.50/1.00  --qbf_pred_elim                         true
% 2.50/1.00  --qbf_split                             512
% 2.50/1.00  
% 2.50/1.00  ------ BMC1 Options
% 2.50/1.00  
% 2.50/1.00  --bmc1_incremental                      false
% 2.50/1.00  --bmc1_axioms                           reachable_all
% 2.50/1.00  --bmc1_min_bound                        0
% 2.50/1.00  --bmc1_max_bound                        -1
% 2.50/1.00  --bmc1_max_bound_default                -1
% 2.50/1.00  --bmc1_symbol_reachability              true
% 2.50/1.00  --bmc1_property_lemmas                  false
% 2.50/1.00  --bmc1_k_induction                      false
% 2.50/1.00  --bmc1_non_equiv_states                 false
% 2.50/1.00  --bmc1_deadlock                         false
% 2.50/1.00  --bmc1_ucm                              false
% 2.50/1.00  --bmc1_add_unsat_core                   none
% 2.50/1.00  --bmc1_unsat_core_children              false
% 2.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/1.00  --bmc1_out_stat                         full
% 2.50/1.00  --bmc1_ground_init                      false
% 2.50/1.00  --bmc1_pre_inst_next_state              false
% 2.50/1.00  --bmc1_pre_inst_state                   false
% 2.50/1.00  --bmc1_pre_inst_reach_state             false
% 2.50/1.00  --bmc1_out_unsat_core                   false
% 2.50/1.00  --bmc1_aig_witness_out                  false
% 2.50/1.00  --bmc1_verbose                          false
% 2.50/1.00  --bmc1_dump_clauses_tptp                false
% 2.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.50/1.00  --bmc1_dump_file                        -
% 2.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.50/1.00  --bmc1_ucm_extend_mode                  1
% 2.50/1.00  --bmc1_ucm_init_mode                    2
% 2.50/1.00  --bmc1_ucm_cone_mode                    none
% 2.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.50/1.00  --bmc1_ucm_relax_model                  4
% 2.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/1.00  --bmc1_ucm_layered_model                none
% 2.50/1.00  --bmc1_ucm_max_lemma_size               10
% 2.50/1.00  
% 2.50/1.00  ------ AIG Options
% 2.50/1.00  
% 2.50/1.00  --aig_mode                              false
% 2.50/1.00  
% 2.50/1.00  ------ Instantiation Options
% 2.50/1.00  
% 2.50/1.00  --instantiation_flag                    true
% 2.50/1.00  --inst_sos_flag                         false
% 2.50/1.00  --inst_sos_phase                        true
% 2.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel_side                     none
% 2.50/1.00  --inst_solver_per_active                1400
% 2.50/1.00  --inst_solver_calls_frac                1.
% 2.50/1.00  --inst_passive_queue_type               priority_queues
% 2.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/1.00  --inst_passive_queues_freq              [25;2]
% 2.50/1.00  --inst_dismatching                      true
% 2.50/1.00  --inst_eager_unprocessed_to_passive     true
% 2.50/1.00  --inst_prop_sim_given                   true
% 2.50/1.00  --inst_prop_sim_new                     false
% 2.50/1.00  --inst_subs_new                         false
% 2.50/1.00  --inst_eq_res_simp                      false
% 2.50/1.00  --inst_subs_given                       false
% 2.50/1.00  --inst_orphan_elimination               true
% 2.50/1.00  --inst_learning_loop_flag               true
% 2.50/1.00  --inst_learning_start                   3000
% 2.50/1.00  --inst_learning_factor                  2
% 2.50/1.00  --inst_start_prop_sim_after_learn       3
% 2.50/1.00  --inst_sel_renew                        solver
% 2.50/1.00  --inst_lit_activity_flag                true
% 2.50/1.00  --inst_restr_to_given                   false
% 2.50/1.00  --inst_activity_threshold               500
% 2.50/1.00  --inst_out_proof                        true
% 2.50/1.00  
% 2.50/1.00  ------ Resolution Options
% 2.50/1.00  
% 2.50/1.00  --resolution_flag                       false
% 2.50/1.00  --res_lit_sel                           adaptive
% 2.50/1.00  --res_lit_sel_side                      none
% 2.50/1.00  --res_ordering                          kbo
% 2.50/1.00  --res_to_prop_solver                    active
% 2.50/1.00  --res_prop_simpl_new                    false
% 2.50/1.00  --res_prop_simpl_given                  true
% 2.50/1.00  --res_passive_queue_type                priority_queues
% 2.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/1.00  --res_passive_queues_freq               [15;5]
% 2.50/1.00  --res_forward_subs                      full
% 2.50/1.00  --res_backward_subs                     full
% 2.50/1.00  --res_forward_subs_resolution           true
% 2.50/1.00  --res_backward_subs_resolution          true
% 2.50/1.00  --res_orphan_elimination                true
% 2.50/1.00  --res_time_limit                        2.
% 2.50/1.00  --res_out_proof                         true
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Options
% 2.50/1.00  
% 2.50/1.00  --superposition_flag                    true
% 2.50/1.00  --sup_passive_queue_type                priority_queues
% 2.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.50/1.00  --demod_completeness_check              fast
% 2.50/1.00  --demod_use_ground                      true
% 2.50/1.00  --sup_to_prop_solver                    passive
% 2.50/1.00  --sup_prop_simpl_new                    true
% 2.50/1.00  --sup_prop_simpl_given                  true
% 2.50/1.00  --sup_fun_splitting                     false
% 2.50/1.00  --sup_smt_interval                      50000
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Simplification Setup
% 2.50/1.00  
% 2.50/1.00  --sup_indices_passive                   []
% 2.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_full_bw                           [BwDemod]
% 2.50/1.00  --sup_immed_triv                        [TrivRules]
% 2.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_immed_bw_main                     []
% 2.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  
% 2.50/1.00  ------ Combination Options
% 2.50/1.00  
% 2.50/1.00  --comb_res_mult                         3
% 2.50/1.00  --comb_sup_mult                         2
% 2.50/1.00  --comb_inst_mult                        10
% 2.50/1.00  
% 2.50/1.00  ------ Debug Options
% 2.50/1.00  
% 2.50/1.00  --dbg_backtrace                         false
% 2.50/1.00  --dbg_dump_prop_clauses                 false
% 2.50/1.00  --dbg_dump_prop_clauses_file            -
% 2.50/1.00  --dbg_out_stat                          false
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  ------ Proving...
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  % SZS status Theorem for theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  fof(f17,axiom,(
% 2.50/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f65,plain,(
% 2.50/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f17])).
% 2.50/1.00  
% 2.50/1.00  fof(f7,axiom,(
% 2.50/1.00    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f55,plain,(
% 2.50/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f7])).
% 2.50/1.00  
% 2.50/1.00  fof(f4,axiom,(
% 2.50/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f40,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f4])).
% 2.50/1.00  
% 2.50/1.00  fof(f1,axiom,(
% 2.50/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f37,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.50/1.00    inference(cnf_transformation,[],[f1])).
% 2.50/1.00  
% 2.50/1.00  fof(f71,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f40,f37])).
% 2.50/1.00  
% 2.50/1.00  fof(f10,axiom,(
% 2.50/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f58,plain,(
% 2.50/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f10])).
% 2.50/1.00  
% 2.50/1.00  fof(f72,plain,(
% 2.50/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f55,f71,f58])).
% 2.50/1.00  
% 2.50/1.00  fof(f88,plain,(
% 2.50/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0))))) )),
% 2.50/1.00    inference(definition_unfolding,[],[f65,f72,f72])).
% 2.50/1.00  
% 2.50/1.00  fof(f12,axiom,(
% 2.50/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f60,plain,(
% 2.50/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f12])).
% 2.50/1.00  
% 2.50/1.00  fof(f86,plain,(
% 2.50/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f60,f72])).
% 2.50/1.00  
% 2.50/1.00  fof(f13,axiom,(
% 2.50/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f61,plain,(
% 2.50/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f13])).
% 2.50/1.00  
% 2.50/1.00  fof(f8,axiom,(
% 2.50/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f56,plain,(
% 2.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f8])).
% 2.50/1.00  
% 2.50/1.00  fof(f73,plain,(
% 2.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f56,f71,f58])).
% 2.50/1.00  
% 2.50/1.00  fof(f76,plain,(
% 2.50/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f61,f73])).
% 2.50/1.00  
% 2.50/1.00  fof(f9,axiom,(
% 2.50/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f57,plain,(
% 2.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f9])).
% 2.50/1.00  
% 2.50/1.00  fof(f85,plain,(
% 2.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_enumset1(X0,X1,X2,X3))))) )),
% 2.50/1.00    inference(definition_unfolding,[],[f57,f71,f58,f73])).
% 2.50/1.00  
% 2.50/1.00  fof(f11,axiom,(
% 2.50/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f59,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f11])).
% 2.50/1.00  
% 2.50/1.00  fof(f75,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f59,f72])).
% 2.50/1.00  
% 2.50/1.00  fof(f2,axiom,(
% 2.50/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f22,plain,(
% 2.50/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.50/1.00    inference(ennf_transformation,[],[f2])).
% 2.50/1.00  
% 2.50/1.00  fof(f38,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f22])).
% 2.50/1.00  
% 2.50/1.00  fof(f20,conjecture,(
% 2.50/1.00    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f21,negated_conjecture,(
% 2.50/1.00    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.50/1.00    inference(negated_conjecture,[],[f20])).
% 2.50/1.00  
% 2.50/1.00  fof(f24,plain,(
% 2.50/1.00    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.50/1.00    inference(ennf_transformation,[],[f21])).
% 2.50/1.00  
% 2.50/1.00  fof(f35,plain,(
% 2.50/1.00    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)))),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f36,plain,(
% 2.50/1.00    sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 2.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f35])).
% 2.50/1.00  
% 2.50/1.00  fof(f68,plain,(
% 2.50/1.00    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 2.50/1.00    inference(cnf_transformation,[],[f36])).
% 2.50/1.00  
% 2.50/1.00  fof(f91,plain,(
% 2.50/1.00    r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK3,sK4))),
% 2.50/1.00    inference(definition_unfolding,[],[f68,f58])).
% 2.50/1.00  
% 2.50/1.00  fof(f3,axiom,(
% 2.50/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f39,plain,(
% 2.50/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.50/1.00    inference(cnf_transformation,[],[f3])).
% 2.50/1.00  
% 2.50/1.00  fof(f19,axiom,(
% 2.50/1.00    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f67,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0) )),
% 2.50/1.00    inference(cnf_transformation,[],[f19])).
% 2.50/1.00  
% 2.50/1.00  fof(f90,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k1_xboole_0) )),
% 2.50/1.00    inference(definition_unfolding,[],[f67,f37,f58])).
% 2.50/1.00  
% 2.50/1.00  fof(f18,axiom,(
% 2.50/1.00    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f66,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f18])).
% 2.50/1.00  
% 2.50/1.00  fof(f89,plain,(
% 2.50/1.00    ( ! [X0,X1] : (k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0)) )),
% 2.50/1.00    inference(definition_unfolding,[],[f66,f58,f58])).
% 2.50/1.00  
% 2.50/1.00  fof(f5,axiom,(
% 2.50/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f23,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.50/1.00    inference(ennf_transformation,[],[f5])).
% 2.50/1.00  
% 2.50/1.00  fof(f25,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/1.00    inference(nnf_transformation,[],[f23])).
% 2.50/1.00  
% 2.50/1.00  fof(f26,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/1.00    inference(flattening,[],[f25])).
% 2.50/1.00  
% 2.50/1.00  fof(f27,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/1.00    inference(rectify,[],[f26])).
% 2.50/1.00  
% 2.50/1.00  fof(f28,plain,(
% 2.50/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f29,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.50/1.00  
% 2.50/1.00  fof(f43,plain,(
% 2.50/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.50/1.00    inference(cnf_transformation,[],[f29])).
% 2.50/1.00  
% 2.50/1.00  fof(f82,plain,(
% 2.50/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 2.50/1.00    inference(definition_unfolding,[],[f43,f72])).
% 2.50/1.00  
% 2.50/1.00  fof(f94,plain,(
% 2.50/1.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3) )),
% 2.50/1.00    inference(equality_resolution,[],[f82])).
% 2.50/1.00  
% 2.50/1.00  fof(f95,plain,(
% 2.50/1.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))))) )),
% 2.50/1.00    inference(equality_resolution,[],[f94])).
% 2.50/1.00  
% 2.50/1.00  fof(f6,axiom,(
% 2.50/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f30,plain,(
% 2.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.50/1.00    inference(nnf_transformation,[],[f6])).
% 2.50/1.00  
% 2.50/1.00  fof(f31,plain,(
% 2.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.50/1.00    inference(flattening,[],[f30])).
% 2.50/1.00  
% 2.50/1.00  fof(f32,plain,(
% 2.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.50/1.00    inference(rectify,[],[f31])).
% 2.50/1.00  
% 2.50/1.00  fof(f33,plain,(
% 2.50/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f34,plain,(
% 2.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 2.50/1.00  
% 2.50/1.00  fof(f49,plain,(
% 2.50/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.50/1.00    inference(cnf_transformation,[],[f34])).
% 2.50/1.00  
% 2.50/1.00  fof(f103,plain,(
% 2.50/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 2.50/1.00    inference(equality_resolution,[],[f49])).
% 2.50/1.00  
% 2.50/1.00  fof(f70,plain,(
% 2.50/1.00    sK2 != sK4),
% 2.50/1.00    inference(cnf_transformation,[],[f36])).
% 2.50/1.00  
% 2.50/1.00  fof(f69,plain,(
% 2.50/1.00    sK2 != sK3),
% 2.50/1.00    inference(cnf_transformation,[],[f36])).
% 2.50/1.00  
% 2.50/1.00  cnf(c_21,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0)))) ),
% 2.50/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_19,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2) ),
% 2.50/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2121,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X2,X1) ),
% 2.50/1.00      inference(light_normalisation,[status(thm)],[c_21,c_19]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2997,plain,
% 2.50/1.00      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_2121,c_19]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_1,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
% 2.50/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3103,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k3_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X2,X1) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_2997,c_1]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_18,plain,
% 2.50/1.00      ( k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_enumset1(X0,X1,X2,X3)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) ),
% 2.50/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4695,plain,
% 2.50/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_enumset1(X0,X0,X0,X1)))) = k2_enumset1(X0,X0,X2,X1) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_3103,c_18]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_0,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 2.50/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2717,plain,
% 2.50/1.00      ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_19,c_0]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2996,plain,
% 2.50/1.00      ( k2_enumset1(X0,X0,X1,X0) = k2_tarski(X0,X1) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_2121,c_0]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3501,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_enumset1(X0,X1,X0,X2),k3_xboole_0(k2_enumset1(X0,X1,X0,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_2996,c_18]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3527,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X0,X2) ),
% 2.50/1.00      inference(demodulation,[status(thm)],[c_3501,c_1]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4700,plain,
% 2.50/1.00      ( k2_enumset1(X0,X1,X0,X2) = k2_enumset1(X0,X0,X2,X1) ),
% 2.50/1.00      inference(light_normalisation,[status(thm)],[c_4695,c_2717,c_3527]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2,plain,
% 2.50/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.50/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_26,negated_conjecture,
% 2.50/1.00      ( r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK3,sK4)) ),
% 2.50/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_191,plain,
% 2.50/1.00      ( k3_xboole_0(X0,X1) = X0
% 2.50/1.00      | k2_tarski(sK3,sK4) != X1
% 2.50/1.00      | k2_tarski(sK2,sK2) != X0 ),
% 2.50/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_192,plain,
% 2.50/1.00      ( k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK3,sK4)) = k2_tarski(sK2,sK2) ),
% 2.50/1.00      inference(unflattening,[status(thm)],[c_191]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3761,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(sK3,sK4),k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK2,sK2))) = k2_enumset1(sK3,sK4,sK3,sK2) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_192,c_3527]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3,plain,
% 2.50/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.50/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_23,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k1_xboole_0 ),
% 2.50/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_22,plain,
% 2.50/1.00      ( k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
% 2.50/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2069,plain,
% 2.50/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k1_xboole_0 ),
% 2.50/1.00      inference(light_normalisation,[status(thm)],[c_23,c_22]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3769,plain,
% 2.50/1.00      ( k2_enumset1(sK3,sK4,sK3,sK2) = k2_tarski(sK3,sK4) ),
% 2.50/1.00      inference(demodulation,[status(thm)],[c_3761,c_3,c_2069]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4036,plain,
% 2.50/1.00      ( k5_xboole_0(k2_enumset1(X0,sK3,sK4,sK3),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_enumset1(X0,sK3,sK4,sK3)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k2_tarski(X0,X0)))) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_3769,c_18]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4044,plain,
% 2.50/1.00      ( k5_xboole_0(k2_enumset1(X0,sK3,sK4,sK3),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_enumset1(X0,sK3,sK4,sK3)))) = k2_enumset1(X0,X0,sK4,sK3) ),
% 2.50/1.00      inference(demodulation,[status(thm)],[c_4036,c_2121]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_5173,plain,
% 2.50/1.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)))) = k2_enumset1(sK4,sK4,sK4,sK3) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_4700,c_4044]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3512,plain,
% 2.50/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_18,c_1]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3763,plain,
% 2.50/1.00      ( k2_enumset1(X0,X0,X1,X1) = k2_enumset1(X0,X0,X0,X1) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_3527,c_2121]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_3766,plain,
% 2.50/1.00      ( k2_enumset1(X0,X0,X1,X1) = k2_tarski(X0,X1) ),
% 2.50/1.00      inference(light_normalisation,[status(thm)],[c_3763,c_2717]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_5225,plain,
% 2.50/1.00      ( k2_enumset1(sK4,sK3,sK4,sK2) = k2_tarski(sK4,sK3) ),
% 2.50/1.00      inference(demodulation,
% 2.50/1.00                [status(thm)],
% 2.50/1.00                [c_5173,c_2717,c_3512,c_3527,c_3766]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_5341,plain,
% 2.50/1.00      ( k2_enumset1(sK4,sK4,sK2,sK3) = k2_tarski(sK4,sK3) ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_5225,c_4700]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_9,plain,
% 2.50/1.00      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) ),
% 2.50/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2049,plain,
% 2.50/1.00      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) = iProver_top ),
% 2.50/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2089,plain,
% 2.50/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 2.50/1.00      inference(demodulation,[status(thm)],[c_19,c_2049]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_5373,plain,
% 2.50/1.00      ( r2_hidden(sK2,k2_tarski(sK4,sK3)) = iProver_top ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_5341,c_2089]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_17,plain,
% 2.50/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 2.50/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2209,plain,
% 2.50/1.00      ( ~ r2_hidden(sK2,k2_tarski(sK4,X0)) | sK2 = X0 | sK2 = sK4 ),
% 2.50/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2273,plain,
% 2.50/1.00      ( ~ r2_hidden(sK2,k2_tarski(sK4,sK3)) | sK2 = sK3 | sK2 = sK4 ),
% 2.50/1.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_2274,plain,
% 2.50/1.00      ( sK2 = sK3
% 2.50/1.00      | sK2 = sK4
% 2.50/1.00      | r2_hidden(sK2,k2_tarski(sK4,sK3)) != iProver_top ),
% 2.50/1.00      inference(predicate_to_equality,[status(thm)],[c_2273]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_24,negated_conjecture,
% 2.50/1.00      ( sK2 != sK4 ),
% 2.50/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_25,negated_conjecture,
% 2.50/1.00      ( sK2 != sK3 ),
% 2.50/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(contradiction,plain,
% 2.50/1.00      ( $false ),
% 2.50/1.00      inference(minisat,[status(thm)],[c_5373,c_2274,c_24,c_25]) ).
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  ------                               Statistics
% 2.50/1.00  
% 2.50/1.00  ------ General
% 2.50/1.00  
% 2.50/1.00  abstr_ref_over_cycles:                  0
% 2.50/1.00  abstr_ref_under_cycles:                 0
% 2.50/1.00  gc_basic_clause_elim:                   0
% 2.50/1.00  forced_gc_time:                         0
% 2.50/1.00  parsing_time:                           0.009
% 2.50/1.00  unif_index_cands_time:                  0.
% 2.50/1.00  unif_index_add_time:                    0.
% 2.50/1.00  orderings_time:                         0.
% 2.50/1.00  out_proof_time:                         0.008
% 2.50/1.00  total_time:                             0.205
% 2.50/1.00  num_of_symbols:                         44
% 2.50/1.00  num_of_terms:                           6665
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing
% 2.50/1.00  
% 2.50/1.00  num_of_splits:                          0
% 2.50/1.00  num_of_split_atoms:                     0
% 2.50/1.00  num_of_reused_defs:                     0
% 2.50/1.00  num_eq_ax_congr_red:                    57
% 2.50/1.00  num_of_sem_filtered_clauses:            1
% 2.50/1.00  num_of_subtypes:                        0
% 2.50/1.00  monotx_restored_types:                  0
% 2.50/1.00  sat_num_of_epr_types:                   0
% 2.50/1.00  sat_num_of_non_cyclic_types:            0
% 2.50/1.00  sat_guarded_non_collapsed_types:        0
% 2.50/1.00  num_pure_diseq_elim:                    0
% 2.50/1.00  simp_replaced_by:                       0
% 2.50/1.00  res_preprocessed:                       118
% 2.50/1.00  prep_upred:                             0
% 2.50/1.00  prep_unflattend:                        98
% 2.50/1.00  smt_new_axioms:                         0
% 2.50/1.00  pred_elim_cands:                        1
% 2.50/1.00  pred_elim:                              1
% 2.50/1.00  pred_elim_cl:                           1
% 2.50/1.00  pred_elim_cycles:                       3
% 2.50/1.00  merged_defs:                            0
% 2.50/1.00  merged_defs_ncl:                        0
% 2.50/1.00  bin_hyper_res:                          0
% 2.50/1.00  prep_cycles:                            4
% 2.50/1.00  pred_elim_time:                         0.037
% 2.50/1.00  splitting_time:                         0.
% 2.50/1.00  sem_filter_time:                        0.
% 2.50/1.00  monotx_time:                            0.
% 2.50/1.00  subtype_inf_time:                       0.
% 2.50/1.00  
% 2.50/1.00  ------ Problem properties
% 2.50/1.00  
% 2.50/1.00  clauses:                                26
% 2.50/1.00  conjectures:                            2
% 2.50/1.00  epr:                                    2
% 2.50/1.00  horn:                                   22
% 2.50/1.00  ground:                                 3
% 2.50/1.00  unary:                                  17
% 2.50/1.00  binary:                                 0
% 2.50/1.00  lits:                                   48
% 2.50/1.00  lits_eq:                                34
% 2.50/1.00  fd_pure:                                0
% 2.50/1.00  fd_pseudo:                              0
% 2.50/1.00  fd_cond:                                0
% 2.50/1.00  fd_pseudo_cond:                         7
% 2.50/1.00  ac_symbols:                             0
% 2.50/1.00  
% 2.50/1.00  ------ Propositional Solver
% 2.50/1.00  
% 2.50/1.00  prop_solver_calls:                      26
% 2.50/1.00  prop_fast_solver_calls:                 842
% 2.50/1.00  smt_solver_calls:                       0
% 2.50/1.00  smt_fast_solver_calls:                  0
% 2.50/1.00  prop_num_of_clauses:                    1532
% 2.50/1.00  prop_preprocess_simplified:             5836
% 2.50/1.00  prop_fo_subsumed:                       0
% 2.50/1.00  prop_solver_time:                       0.
% 2.50/1.00  smt_solver_time:                        0.
% 2.50/1.00  smt_fast_solver_time:                   0.
% 2.50/1.00  prop_fast_solver_time:                  0.
% 2.50/1.00  prop_unsat_core_time:                   0.
% 2.50/1.00  
% 2.50/1.00  ------ QBF
% 2.50/1.00  
% 2.50/1.00  qbf_q_res:                              0
% 2.50/1.00  qbf_num_tautologies:                    0
% 2.50/1.00  qbf_prep_cycles:                        0
% 2.50/1.00  
% 2.50/1.00  ------ BMC1
% 2.50/1.00  
% 2.50/1.00  bmc1_current_bound:                     -1
% 2.50/1.00  bmc1_last_solved_bound:                 -1
% 2.50/1.00  bmc1_unsat_core_size:                   -1
% 2.50/1.00  bmc1_unsat_core_parents_size:           -1
% 2.50/1.00  bmc1_merge_next_fun:                    0
% 2.50/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.50/1.00  
% 2.50/1.00  ------ Instantiation
% 2.50/1.00  
% 2.50/1.00  inst_num_of_clauses:                    482
% 2.50/1.00  inst_num_in_passive:                    127
% 2.50/1.00  inst_num_in_active:                     204
% 2.50/1.00  inst_num_in_unprocessed:                151
% 2.50/1.00  inst_num_of_loops:                      210
% 2.50/1.00  inst_num_of_learning_restarts:          0
% 2.50/1.00  inst_num_moves_active_passive:          5
% 2.50/1.00  inst_lit_activity:                      0
% 2.50/1.00  inst_lit_activity_moves:                0
% 2.50/1.00  inst_num_tautologies:                   0
% 2.50/1.00  inst_num_prop_implied:                  0
% 2.50/1.00  inst_num_existing_simplified:           0
% 2.50/1.00  inst_num_eq_res_simplified:             0
% 2.50/1.00  inst_num_child_elim:                    0
% 2.50/1.00  inst_num_of_dismatching_blockings:      158
% 2.50/1.00  inst_num_of_non_proper_insts:           471
% 2.50/1.00  inst_num_of_duplicates:                 0
% 2.50/1.00  inst_inst_num_from_inst_to_res:         0
% 2.50/1.00  inst_dismatching_checking_time:         0.
% 2.50/1.00  
% 2.50/1.00  ------ Resolution
% 2.50/1.00  
% 2.50/1.00  res_num_of_clauses:                     0
% 2.50/1.00  res_num_in_passive:                     0
% 2.50/1.00  res_num_in_active:                      0
% 2.50/1.00  res_num_of_loops:                       122
% 2.50/1.00  res_forward_subset_subsumed:            70
% 2.50/1.00  res_backward_subset_subsumed:           0
% 2.50/1.00  res_forward_subsumed:                   0
% 2.50/1.00  res_backward_subsumed:                  0
% 2.50/1.00  res_forward_subsumption_resolution:     0
% 2.50/1.00  res_backward_subsumption_resolution:    0
% 2.50/1.00  res_clause_to_clause_subsumption:       683
% 2.50/1.00  res_orphan_elimination:                 0
% 2.50/1.00  res_tautology_del:                      12
% 2.50/1.00  res_num_eq_res_simplified:              0
% 2.50/1.00  res_num_sel_changes:                    0
% 2.50/1.00  res_moves_from_active_to_pass:          0
% 2.50/1.00  
% 2.50/1.00  ------ Superposition
% 2.50/1.00  
% 2.50/1.00  sup_time_total:                         0.
% 2.50/1.00  sup_time_generating:                    0.
% 2.50/1.00  sup_time_sim_full:                      0.
% 2.50/1.00  sup_time_sim_immed:                     0.
% 2.50/1.00  
% 2.50/1.00  sup_num_of_clauses:                     85
% 2.50/1.00  sup_num_in_active:                      42
% 2.50/1.00  sup_num_in_passive:                     43
% 2.50/1.00  sup_num_of_loops:                       41
% 2.50/1.00  sup_fw_superposition:                   114
% 2.50/1.00  sup_bw_superposition:                   157
% 2.50/1.00  sup_immediate_simplified:               68
% 2.50/1.00  sup_given_eliminated:                   0
% 2.50/1.00  comparisons_done:                       0
% 2.50/1.00  comparisons_avoided:                    3
% 2.50/1.00  
% 2.50/1.00  ------ Simplifications
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  sim_fw_subset_subsumed:                 0
% 2.50/1.00  sim_bw_subset_subsumed:                 0
% 2.50/1.00  sim_fw_subsumed:                        21
% 2.50/1.00  sim_bw_subsumed:                        0
% 2.50/1.00  sim_fw_subsumption_res:                 0
% 2.50/1.00  sim_bw_subsumption_res:                 0
% 2.50/1.00  sim_tautology_del:                      0
% 2.50/1.00  sim_eq_tautology_del:                   7
% 2.50/1.00  sim_eq_res_simp:                        0
% 2.50/1.00  sim_fw_demodulated:                     27
% 2.50/1.00  sim_bw_demodulated:                     3
% 2.50/1.00  sim_light_normalised:                   37
% 2.50/1.00  sim_joinable_taut:                      0
% 2.50/1.00  sim_joinable_simp:                      0
% 2.50/1.00  sim_ac_normalised:                      0
% 2.50/1.00  sim_smt_subsumption:                    0
% 2.50/1.00  
%------------------------------------------------------------------------------
