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
% DateTime   : Thu Dec  3 11:34:00 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  219 (26099 expanded)
%              Number of clauses        :  138 (7230 expanded)
%              Number of leaves         :   28 (7560 expanded)
%              Depth                    :   43
%              Number of atoms          :  404 (26852 expanded)
%              Number of equality atoms :  297 (26624 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f79])).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f58,f80])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f24])).

fof(f40,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f40])).

fof(f75,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f80])).

fof(f92,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f75,f58,f81])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f99,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f100,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f99])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f101,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f90])).

cnf(c_1210,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2245,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_36941,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_36952,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_36941])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1204,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_23,c_13,c_1])).

cnf(c_2124,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_1204])).

cnf(c_24,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1203,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_24,c_13,c_1])).

cnf(c_1842,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_1203])).

cnf(c_2133,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1842,c_13])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1953,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_2139,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2133,c_1953])).

cnf(c_2687,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_2139])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2688,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_2139])).

cnf(c_2697,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_2688,c_12])).

cnf(c_2704,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2697,c_2139])).

cnf(c_2822,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2687,c_2704])).

cnf(c_1635,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_4456,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_1635])).

cnf(c_4513,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4456,c_12])).

cnf(c_2715,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2704,c_13])).

cnf(c_4578,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_4513,c_2715])).

cnf(c_7174,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2704,c_4578])).

cnf(c_7363,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_7174,c_7174])).

cnf(c_1636,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_4891,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2704,c_1636])).

cnf(c_5231,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4891,c_1])).

cnf(c_7397,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_7363,c_2704,c_5231])).

cnf(c_7606,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_7397])).

cnf(c_7333,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_4513,c_7174])).

cnf(c_2135,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_14])).

cnf(c_3080,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2715,c_2135])).

cnf(c_5541,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3080,c_1636])).

cnf(c_5555,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_5541,c_12])).

cnf(c_15512,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(sK3,X0))),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_7333,c_5555])).

cnf(c_15696,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_15512,c_2704])).

cnf(c_19097,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_7606,c_15696])).

cnf(c_29647,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_2822,c_19097])).

cnf(c_2713,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2135,c_2704])).

cnf(c_2718,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2713,c_12])).

cnf(c_3283,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1,c_2718])).

cnf(c_4054,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_3283,c_2822])).

cnf(c_2707,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_2704])).

cnf(c_4060,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_4054,c_2707])).

cnf(c_4565,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_4513,c_13])).

cnf(c_13647,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_13,c_4565])).

cnf(c_28289,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
    inference(superposition,[status(thm)],[c_13647,c_2822])).

cnf(c_30031,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_29647,c_2704,c_4060,c_28289])).

cnf(c_35441,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_2124,c_30031])).

cnf(c_11,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1609,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2285,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1609])).

cnf(c_3770,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_2285])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1611,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_32928,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_3770,c_1611])).

cnf(c_4923,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1636,c_2704])).

cnf(c_5348,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k5_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2822,c_4923])).

cnf(c_5386,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_5348,c_2704])).

cnf(c_3517,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_3283,c_13])).

cnf(c_7601,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_4891,c_7397])).

cnf(c_7698,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_7601,c_2704,c_5231])).

cnf(c_11014,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(k5_xboole_0(X1,sK3),X0)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_3517,c_7698])).

cnf(c_11106,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,sK3),X0)) = k5_xboole_0(sK3,X1) ),
    inference(light_normalisation,[status(thm)],[c_11014,c_2704])).

cnf(c_11970,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),X1),k5_xboole_0(sK3,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_11106,c_4513])).

cnf(c_22838,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),X1),sK3),X2),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_2715,c_11970])).

cnf(c_2714,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2704,c_2135])).

cnf(c_3052,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2714,c_2704])).

cnf(c_3054,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(demodulation,[status(thm)],[c_3052,c_12])).

cnf(c_3325,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = sK3 ),
    inference(superposition,[status(thm)],[c_2715,c_3054])).

cnf(c_6971,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),X1),sK3) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3325,c_4513])).

cnf(c_23335,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(light_normalisation,[status(thm)],[c_22838,c_13,c_6971])).

cnf(c_34408,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_5386,c_23335])).

cnf(c_34856,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_34408,c_32928])).

cnf(c_4896,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_3283,c_1636])).

cnf(c_34857,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34856,c_14,c_4896])).

cnf(c_2711,plain,
    ( k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1204,c_2704])).

cnf(c_7584,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))),k5_xboole_0(sK3,X0)) = k3_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2711,c_7397])).

cnf(c_7715,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),k5_xboole_0(sK3,X0)) = k3_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_7584,c_2704,c_5231])).

cnf(c_12168,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,X0)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_7715,c_7333])).

cnf(c_12268,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,X0)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12168,c_2704])).

cnf(c_12972,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))),X0) = k5_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_12268,c_7174])).

cnf(c_12989,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))),X0) = k3_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_12972,c_2704])).

cnf(c_13994,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X0) = k3_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2711,c_12989])).

cnf(c_27115,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X0) = k3_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_13994])).

cnf(c_12167,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_7397,c_7333])).

cnf(c_12269,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_12167,c_2704,c_5231])).

cnf(c_12446,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)),k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2822,c_12269])).

cnf(c_12131,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_2822,c_7333])).

cnf(c_12277,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_12131,c_2704])).

cnf(c_12577,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_12446,c_2704,c_12277])).

cnf(c_35052,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_27115,c_12577])).

cnf(c_35053,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35052,c_32928,c_34857])).

cnf(c_35054,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35053,c_1953])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1610,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20531,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1610,c_1611])).

cnf(c_35055,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35054,c_12,c_20531])).

cnf(c_35458,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35441,c_32928,c_34857,c_35055])).

cnf(c_28262,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_13647,c_13])).

cnf(c_13825,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_4565,c_4565])).

cnf(c_28421,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_28262,c_13825])).

cnf(c_35459,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35458,c_1953,c_28421])).

cnf(c_28045,plain,
    ( k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1204,c_13647])).

cnf(c_35460,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35459,c_28045])).

cnf(c_35461,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35460,c_20531])).

cnf(c_35462,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35461,c_12,c_1953])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1615,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_36403,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_35462,c_1615])).

cnf(c_36410,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_36403])).

cnf(c_36412,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ r1_xboole_0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_36410])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1617,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_36396,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_35462,c_1617])).

cnf(c_36407,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_36396])).

cnf(c_36409,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_36407])).

cnf(c_1207,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1691,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_1750,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_1830,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_1831,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1830])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1726,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1681,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1709,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_21,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_30,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_27,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36952,c_36412,c_36409,c_34857,c_1831,c_1726,c_1709,c_30,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.60/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.60/1.99  
% 11.60/1.99  ------  iProver source info
% 11.60/1.99  
% 11.60/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.60/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.60/1.99  git: non_committed_changes: false
% 11.60/1.99  git: last_make_outside_of_git: false
% 11.60/1.99  
% 11.60/1.99  ------ 
% 11.60/1.99  
% 11.60/1.99  ------ Input Options
% 11.60/1.99  
% 11.60/1.99  --out_options                           all
% 11.60/1.99  --tptp_safe_out                         true
% 11.60/1.99  --problem_path                          ""
% 11.60/1.99  --include_path                          ""
% 11.60/1.99  --clausifier                            res/vclausify_rel
% 11.60/1.99  --clausifier_options                    ""
% 11.60/1.99  --stdin                                 false
% 11.60/1.99  --stats_out                             all
% 11.60/1.99  
% 11.60/1.99  ------ General Options
% 11.60/1.99  
% 11.60/1.99  --fof                                   false
% 11.60/1.99  --time_out_real                         305.
% 11.60/1.99  --time_out_virtual                      -1.
% 11.60/1.99  --symbol_type_check                     false
% 11.60/1.99  --clausify_out                          false
% 11.60/1.99  --sig_cnt_out                           false
% 11.60/1.99  --trig_cnt_out                          false
% 11.60/1.99  --trig_cnt_out_tolerance                1.
% 11.60/1.99  --trig_cnt_out_sk_spl                   false
% 11.60/1.99  --abstr_cl_out                          false
% 11.60/1.99  
% 11.60/1.99  ------ Global Options
% 11.60/1.99  
% 11.60/1.99  --schedule                              default
% 11.60/1.99  --add_important_lit                     false
% 11.60/1.99  --prop_solver_per_cl                    1000
% 11.60/1.99  --min_unsat_core                        false
% 11.60/1.99  --soft_assumptions                      false
% 11.60/1.99  --soft_lemma_size                       3
% 11.60/1.99  --prop_impl_unit_size                   0
% 11.60/1.99  --prop_impl_unit                        []
% 11.60/1.99  --share_sel_clauses                     true
% 11.60/1.99  --reset_solvers                         false
% 11.60/1.99  --bc_imp_inh                            [conj_cone]
% 11.60/1.99  --conj_cone_tolerance                   3.
% 11.60/1.99  --extra_neg_conj                        none
% 11.60/1.99  --large_theory_mode                     true
% 11.60/1.99  --prolific_symb_bound                   200
% 11.60/1.99  --lt_threshold                          2000
% 11.60/1.99  --clause_weak_htbl                      true
% 11.60/1.99  --gc_record_bc_elim                     false
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing Options
% 11.60/1.99  
% 11.60/1.99  --preprocessing_flag                    true
% 11.60/1.99  --time_out_prep_mult                    0.1
% 11.60/1.99  --splitting_mode                        input
% 11.60/1.99  --splitting_grd                         true
% 11.60/1.99  --splitting_cvd                         false
% 11.60/1.99  --splitting_cvd_svl                     false
% 11.60/1.99  --splitting_nvd                         32
% 11.60/1.99  --sub_typing                            true
% 11.60/1.99  --prep_gs_sim                           true
% 11.60/1.99  --prep_unflatten                        true
% 11.60/1.99  --prep_res_sim                          true
% 11.60/1.99  --prep_upred                            true
% 11.60/1.99  --prep_sem_filter                       exhaustive
% 11.60/1.99  --prep_sem_filter_out                   false
% 11.60/1.99  --pred_elim                             true
% 11.60/1.99  --res_sim_input                         true
% 11.60/1.99  --eq_ax_congr_red                       true
% 11.60/1.99  --pure_diseq_elim                       true
% 11.60/1.99  --brand_transform                       false
% 11.60/1.99  --non_eq_to_eq                          false
% 11.60/1.99  --prep_def_merge                        true
% 11.60/1.99  --prep_def_merge_prop_impl              false
% 11.60/1.99  --prep_def_merge_mbd                    true
% 11.60/1.99  --prep_def_merge_tr_red                 false
% 11.60/1.99  --prep_def_merge_tr_cl                  false
% 11.60/1.99  --smt_preprocessing                     true
% 11.60/1.99  --smt_ac_axioms                         fast
% 11.60/1.99  --preprocessed_out                      false
% 11.60/1.99  --preprocessed_stats                    false
% 11.60/1.99  
% 11.60/1.99  ------ Abstraction refinement Options
% 11.60/1.99  
% 11.60/1.99  --abstr_ref                             []
% 11.60/1.99  --abstr_ref_prep                        false
% 11.60/1.99  --abstr_ref_until_sat                   false
% 11.60/1.99  --abstr_ref_sig_restrict                funpre
% 11.60/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.60/1.99  --abstr_ref_under                       []
% 11.60/1.99  
% 11.60/1.99  ------ SAT Options
% 11.60/1.99  
% 11.60/1.99  --sat_mode                              false
% 11.60/1.99  --sat_fm_restart_options                ""
% 11.60/1.99  --sat_gr_def                            false
% 11.60/1.99  --sat_epr_types                         true
% 11.60/1.99  --sat_non_cyclic_types                  false
% 11.60/1.99  --sat_finite_models                     false
% 11.60/1.99  --sat_fm_lemmas                         false
% 11.60/1.99  --sat_fm_prep                           false
% 11.60/1.99  --sat_fm_uc_incr                        true
% 11.60/1.99  --sat_out_model                         small
% 11.60/1.99  --sat_out_clauses                       false
% 11.60/1.99  
% 11.60/1.99  ------ QBF Options
% 11.60/1.99  
% 11.60/1.99  --qbf_mode                              false
% 11.60/1.99  --qbf_elim_univ                         false
% 11.60/1.99  --qbf_dom_inst                          none
% 11.60/1.99  --qbf_dom_pre_inst                      false
% 11.60/1.99  --qbf_sk_in                             false
% 11.60/1.99  --qbf_pred_elim                         true
% 11.60/1.99  --qbf_split                             512
% 11.60/1.99  
% 11.60/1.99  ------ BMC1 Options
% 11.60/1.99  
% 11.60/1.99  --bmc1_incremental                      false
% 11.60/1.99  --bmc1_axioms                           reachable_all
% 11.60/1.99  --bmc1_min_bound                        0
% 11.60/1.99  --bmc1_max_bound                        -1
% 11.60/1.99  --bmc1_max_bound_default                -1
% 11.60/1.99  --bmc1_symbol_reachability              true
% 11.60/1.99  --bmc1_property_lemmas                  false
% 11.60/1.99  --bmc1_k_induction                      false
% 11.60/1.99  --bmc1_non_equiv_states                 false
% 11.60/1.99  --bmc1_deadlock                         false
% 11.60/1.99  --bmc1_ucm                              false
% 11.60/1.99  --bmc1_add_unsat_core                   none
% 11.60/1.99  --bmc1_unsat_core_children              false
% 11.60/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.60/1.99  --bmc1_out_stat                         full
% 11.60/1.99  --bmc1_ground_init                      false
% 11.60/1.99  --bmc1_pre_inst_next_state              false
% 11.60/1.99  --bmc1_pre_inst_state                   false
% 11.60/1.99  --bmc1_pre_inst_reach_state             false
% 11.60/1.99  --bmc1_out_unsat_core                   false
% 11.60/1.99  --bmc1_aig_witness_out                  false
% 11.60/1.99  --bmc1_verbose                          false
% 11.60/1.99  --bmc1_dump_clauses_tptp                false
% 11.60/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.60/1.99  --bmc1_dump_file                        -
% 11.60/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.60/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.60/1.99  --bmc1_ucm_extend_mode                  1
% 11.60/1.99  --bmc1_ucm_init_mode                    2
% 11.60/1.99  --bmc1_ucm_cone_mode                    none
% 11.60/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.60/1.99  --bmc1_ucm_relax_model                  4
% 11.60/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.60/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.60/1.99  --bmc1_ucm_layered_model                none
% 11.60/1.99  --bmc1_ucm_max_lemma_size               10
% 11.60/1.99  
% 11.60/1.99  ------ AIG Options
% 11.60/1.99  
% 11.60/1.99  --aig_mode                              false
% 11.60/1.99  
% 11.60/1.99  ------ Instantiation Options
% 11.60/1.99  
% 11.60/1.99  --instantiation_flag                    true
% 11.60/1.99  --inst_sos_flag                         true
% 11.60/1.99  --inst_sos_phase                        true
% 11.60/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.60/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.60/1.99  --inst_lit_sel_side                     num_symb
% 11.60/1.99  --inst_solver_per_active                1400
% 11.60/1.99  --inst_solver_calls_frac                1.
% 11.60/1.99  --inst_passive_queue_type               priority_queues
% 11.60/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.60/1.99  --inst_passive_queues_freq              [25;2]
% 11.60/1.99  --inst_dismatching                      true
% 11.60/1.99  --inst_eager_unprocessed_to_passive     true
% 11.60/1.99  --inst_prop_sim_given                   true
% 11.60/1.99  --inst_prop_sim_new                     false
% 11.60/1.99  --inst_subs_new                         false
% 11.60/1.99  --inst_eq_res_simp                      false
% 11.60/1.99  --inst_subs_given                       false
% 11.60/1.99  --inst_orphan_elimination               true
% 11.60/1.99  --inst_learning_loop_flag               true
% 11.60/1.99  --inst_learning_start                   3000
% 11.60/1.99  --inst_learning_factor                  2
% 11.60/1.99  --inst_start_prop_sim_after_learn       3
% 11.60/1.99  --inst_sel_renew                        solver
% 11.60/1.99  --inst_lit_activity_flag                true
% 11.60/1.99  --inst_restr_to_given                   false
% 11.60/1.99  --inst_activity_threshold               500
% 11.60/1.99  --inst_out_proof                        true
% 11.60/1.99  
% 11.60/1.99  ------ Resolution Options
% 11.60/1.99  
% 11.60/1.99  --resolution_flag                       true
% 11.60/1.99  --res_lit_sel                           adaptive
% 11.60/1.99  --res_lit_sel_side                      none
% 11.60/1.99  --res_ordering                          kbo
% 11.60/1.99  --res_to_prop_solver                    active
% 11.60/1.99  --res_prop_simpl_new                    false
% 11.60/1.99  --res_prop_simpl_given                  true
% 11.60/1.99  --res_passive_queue_type                priority_queues
% 11.60/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.60/1.99  --res_passive_queues_freq               [15;5]
% 11.60/1.99  --res_forward_subs                      full
% 11.60/1.99  --res_backward_subs                     full
% 11.60/1.99  --res_forward_subs_resolution           true
% 11.60/1.99  --res_backward_subs_resolution          true
% 11.60/1.99  --res_orphan_elimination                true
% 11.60/1.99  --res_time_limit                        2.
% 11.60/1.99  --res_out_proof                         true
% 11.60/1.99  
% 11.60/1.99  ------ Superposition Options
% 11.60/1.99  
% 11.60/1.99  --superposition_flag                    true
% 11.60/1.99  --sup_passive_queue_type                priority_queues
% 11.60/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.60/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.60/1.99  --demod_completeness_check              fast
% 11.60/1.99  --demod_use_ground                      true
% 11.60/1.99  --sup_to_prop_solver                    passive
% 11.60/1.99  --sup_prop_simpl_new                    true
% 11.60/1.99  --sup_prop_simpl_given                  true
% 11.60/1.99  --sup_fun_splitting                     true
% 11.60/1.99  --sup_smt_interval                      50000
% 11.60/1.99  
% 11.60/1.99  ------ Superposition Simplification Setup
% 11.60/1.99  
% 11.60/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.60/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.60/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.60/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.60/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.60/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.60/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.60/1.99  --sup_immed_triv                        [TrivRules]
% 11.60/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.99  --sup_immed_bw_main                     []
% 11.60/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.60/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.60/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.99  --sup_input_bw                          []
% 11.60/1.99  
% 11.60/1.99  ------ Combination Options
% 11.60/1.99  
% 11.60/1.99  --comb_res_mult                         3
% 11.60/1.99  --comb_sup_mult                         2
% 11.60/1.99  --comb_inst_mult                        10
% 11.60/1.99  
% 11.60/1.99  ------ Debug Options
% 11.60/1.99  
% 11.60/1.99  --dbg_backtrace                         false
% 11.60/1.99  --dbg_dump_prop_clauses                 false
% 11.60/1.99  --dbg_dump_prop_clauses_file            -
% 11.60/1.99  --dbg_out_stat                          false
% 11.60/1.99  ------ Parsing...
% 11.60/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.60/1.99  ------ Proving...
% 11.60/1.99  ------ Problem Properties 
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  clauses                                 24
% 11.60/1.99  conjectures                             1
% 11.60/1.99  EPR                                     3
% 11.60/1.99  Horn                                    21
% 11.60/1.99  unary                                   13
% 11.60/1.99  binary                                  5
% 11.60/1.99  lits                                    44
% 11.60/1.99  lits eq                                 24
% 11.60/1.99  fd_pure                                 0
% 11.60/1.99  fd_pseudo                               0
% 11.60/1.99  fd_cond                                 0
% 11.60/1.99  fd_pseudo_cond                          5
% 11.60/1.99  AC symbols                              1
% 11.60/1.99  
% 11.60/1.99  ------ Schedule dynamic 5 is on 
% 11.60/1.99  
% 11.60/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  ------ 
% 11.60/1.99  Current options:
% 11.60/1.99  ------ 
% 11.60/1.99  
% 11.60/1.99  ------ Input Options
% 11.60/1.99  
% 11.60/1.99  --out_options                           all
% 11.60/1.99  --tptp_safe_out                         true
% 11.60/1.99  --problem_path                          ""
% 11.60/1.99  --include_path                          ""
% 11.60/1.99  --clausifier                            res/vclausify_rel
% 11.60/1.99  --clausifier_options                    ""
% 11.60/1.99  --stdin                                 false
% 11.60/1.99  --stats_out                             all
% 11.60/1.99  
% 11.60/1.99  ------ General Options
% 11.60/1.99  
% 11.60/1.99  --fof                                   false
% 11.60/1.99  --time_out_real                         305.
% 11.60/1.99  --time_out_virtual                      -1.
% 11.60/1.99  --symbol_type_check                     false
% 11.60/1.99  --clausify_out                          false
% 11.60/1.99  --sig_cnt_out                           false
% 11.60/1.99  --trig_cnt_out                          false
% 11.60/1.99  --trig_cnt_out_tolerance                1.
% 11.60/1.99  --trig_cnt_out_sk_spl                   false
% 11.60/1.99  --abstr_cl_out                          false
% 11.60/1.99  
% 11.60/1.99  ------ Global Options
% 11.60/1.99  
% 11.60/1.99  --schedule                              default
% 11.60/1.99  --add_important_lit                     false
% 11.60/1.99  --prop_solver_per_cl                    1000
% 11.60/1.99  --min_unsat_core                        false
% 11.60/1.99  --soft_assumptions                      false
% 11.60/1.99  --soft_lemma_size                       3
% 11.60/1.99  --prop_impl_unit_size                   0
% 11.60/1.99  --prop_impl_unit                        []
% 11.60/1.99  --share_sel_clauses                     true
% 11.60/1.99  --reset_solvers                         false
% 11.60/1.99  --bc_imp_inh                            [conj_cone]
% 11.60/1.99  --conj_cone_tolerance                   3.
% 11.60/1.99  --extra_neg_conj                        none
% 11.60/1.99  --large_theory_mode                     true
% 11.60/1.99  --prolific_symb_bound                   200
% 11.60/1.99  --lt_threshold                          2000
% 11.60/1.99  --clause_weak_htbl                      true
% 11.60/1.99  --gc_record_bc_elim                     false
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing Options
% 11.60/1.99  
% 11.60/1.99  --preprocessing_flag                    true
% 11.60/1.99  --time_out_prep_mult                    0.1
% 11.60/1.99  --splitting_mode                        input
% 11.60/1.99  --splitting_grd                         true
% 11.60/1.99  --splitting_cvd                         false
% 11.60/1.99  --splitting_cvd_svl                     false
% 11.60/1.99  --splitting_nvd                         32
% 11.60/1.99  --sub_typing                            true
% 11.60/1.99  --prep_gs_sim                           true
% 11.60/1.99  --prep_unflatten                        true
% 11.60/1.99  --prep_res_sim                          true
% 11.60/1.99  --prep_upred                            true
% 11.60/1.99  --prep_sem_filter                       exhaustive
% 11.60/1.99  --prep_sem_filter_out                   false
% 11.60/1.99  --pred_elim                             true
% 11.60/1.99  --res_sim_input                         true
% 11.60/1.99  --eq_ax_congr_red                       true
% 11.60/1.99  --pure_diseq_elim                       true
% 11.60/1.99  --brand_transform                       false
% 11.60/1.99  --non_eq_to_eq                          false
% 11.60/1.99  --prep_def_merge                        true
% 11.60/1.99  --prep_def_merge_prop_impl              false
% 11.60/1.99  --prep_def_merge_mbd                    true
% 11.60/1.99  --prep_def_merge_tr_red                 false
% 11.60/1.99  --prep_def_merge_tr_cl                  false
% 11.60/1.99  --smt_preprocessing                     true
% 11.60/1.99  --smt_ac_axioms                         fast
% 11.60/1.99  --preprocessed_out                      false
% 11.60/1.99  --preprocessed_stats                    false
% 11.60/1.99  
% 11.60/1.99  ------ Abstraction refinement Options
% 11.60/1.99  
% 11.60/1.99  --abstr_ref                             []
% 11.60/1.99  --abstr_ref_prep                        false
% 11.60/1.99  --abstr_ref_until_sat                   false
% 11.60/1.99  --abstr_ref_sig_restrict                funpre
% 11.60/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.60/1.99  --abstr_ref_under                       []
% 11.60/1.99  
% 11.60/1.99  ------ SAT Options
% 11.60/1.99  
% 11.60/1.99  --sat_mode                              false
% 11.60/1.99  --sat_fm_restart_options                ""
% 11.60/1.99  --sat_gr_def                            false
% 11.60/1.99  --sat_epr_types                         true
% 11.60/1.99  --sat_non_cyclic_types                  false
% 11.60/1.99  --sat_finite_models                     false
% 11.60/1.99  --sat_fm_lemmas                         false
% 11.60/1.99  --sat_fm_prep                           false
% 11.60/1.99  --sat_fm_uc_incr                        true
% 11.60/1.99  --sat_out_model                         small
% 11.60/1.99  --sat_out_clauses                       false
% 11.60/1.99  
% 11.60/1.99  ------ QBF Options
% 11.60/1.99  
% 11.60/1.99  --qbf_mode                              false
% 11.60/1.99  --qbf_elim_univ                         false
% 11.60/1.99  --qbf_dom_inst                          none
% 11.60/1.99  --qbf_dom_pre_inst                      false
% 11.60/1.99  --qbf_sk_in                             false
% 11.60/1.99  --qbf_pred_elim                         true
% 11.60/1.99  --qbf_split                             512
% 11.60/1.99  
% 11.60/1.99  ------ BMC1 Options
% 11.60/1.99  
% 11.60/1.99  --bmc1_incremental                      false
% 11.60/1.99  --bmc1_axioms                           reachable_all
% 11.60/1.99  --bmc1_min_bound                        0
% 11.60/1.99  --bmc1_max_bound                        -1
% 11.60/1.99  --bmc1_max_bound_default                -1
% 11.60/1.99  --bmc1_symbol_reachability              true
% 11.60/1.99  --bmc1_property_lemmas                  false
% 11.60/1.99  --bmc1_k_induction                      false
% 11.60/1.99  --bmc1_non_equiv_states                 false
% 11.60/1.99  --bmc1_deadlock                         false
% 11.60/1.99  --bmc1_ucm                              false
% 11.60/1.99  --bmc1_add_unsat_core                   none
% 11.60/1.99  --bmc1_unsat_core_children              false
% 11.60/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.60/1.99  --bmc1_out_stat                         full
% 11.60/1.99  --bmc1_ground_init                      false
% 11.60/1.99  --bmc1_pre_inst_next_state              false
% 11.60/1.99  --bmc1_pre_inst_state                   false
% 11.60/1.99  --bmc1_pre_inst_reach_state             false
% 11.60/1.99  --bmc1_out_unsat_core                   false
% 11.60/1.99  --bmc1_aig_witness_out                  false
% 11.60/1.99  --bmc1_verbose                          false
% 11.60/1.99  --bmc1_dump_clauses_tptp                false
% 11.60/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.60/1.99  --bmc1_dump_file                        -
% 11.60/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.60/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.60/1.99  --bmc1_ucm_extend_mode                  1
% 11.60/1.99  --bmc1_ucm_init_mode                    2
% 11.60/1.99  --bmc1_ucm_cone_mode                    none
% 11.60/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.60/1.99  --bmc1_ucm_relax_model                  4
% 11.60/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.60/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.60/1.99  --bmc1_ucm_layered_model                none
% 11.60/1.99  --bmc1_ucm_max_lemma_size               10
% 11.60/1.99  
% 11.60/1.99  ------ AIG Options
% 11.60/1.99  
% 11.60/1.99  --aig_mode                              false
% 11.60/1.99  
% 11.60/1.99  ------ Instantiation Options
% 11.60/1.99  
% 11.60/1.99  --instantiation_flag                    true
% 11.60/1.99  --inst_sos_flag                         true
% 11.60/1.99  --inst_sos_phase                        true
% 11.60/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.60/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.60/1.99  --inst_lit_sel_side                     none
% 11.60/1.99  --inst_solver_per_active                1400
% 11.60/1.99  --inst_solver_calls_frac                1.
% 11.60/1.99  --inst_passive_queue_type               priority_queues
% 11.60/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.60/1.99  --inst_passive_queues_freq              [25;2]
% 11.60/1.99  --inst_dismatching                      true
% 11.60/1.99  --inst_eager_unprocessed_to_passive     true
% 11.60/1.99  --inst_prop_sim_given                   true
% 11.60/1.99  --inst_prop_sim_new                     false
% 11.60/1.99  --inst_subs_new                         false
% 11.60/1.99  --inst_eq_res_simp                      false
% 11.60/1.99  --inst_subs_given                       false
% 11.60/1.99  --inst_orphan_elimination               true
% 11.60/1.99  --inst_learning_loop_flag               true
% 11.60/1.99  --inst_learning_start                   3000
% 11.60/1.99  --inst_learning_factor                  2
% 11.60/1.99  --inst_start_prop_sim_after_learn       3
% 11.60/1.99  --inst_sel_renew                        solver
% 11.60/1.99  --inst_lit_activity_flag                true
% 11.60/1.99  --inst_restr_to_given                   false
% 11.60/1.99  --inst_activity_threshold               500
% 11.60/1.99  --inst_out_proof                        true
% 11.60/1.99  
% 11.60/1.99  ------ Resolution Options
% 11.60/1.99  
% 11.60/1.99  --resolution_flag                       false
% 11.60/1.99  --res_lit_sel                           adaptive
% 11.60/1.99  --res_lit_sel_side                      none
% 11.60/1.99  --res_ordering                          kbo
% 11.60/1.99  --res_to_prop_solver                    active
% 11.60/1.99  --res_prop_simpl_new                    false
% 11.60/1.99  --res_prop_simpl_given                  true
% 11.60/1.99  --res_passive_queue_type                priority_queues
% 11.60/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.60/1.99  --res_passive_queues_freq               [15;5]
% 11.60/1.99  --res_forward_subs                      full
% 11.60/1.99  --res_backward_subs                     full
% 11.60/1.99  --res_forward_subs_resolution           true
% 11.60/1.99  --res_backward_subs_resolution          true
% 11.60/1.99  --res_orphan_elimination                true
% 11.60/1.99  --res_time_limit                        2.
% 11.60/1.99  --res_out_proof                         true
% 11.60/1.99  
% 11.60/1.99  ------ Superposition Options
% 11.60/1.99  
% 11.60/1.99  --superposition_flag                    true
% 11.60/1.99  --sup_passive_queue_type                priority_queues
% 11.60/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.60/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.60/1.99  --demod_completeness_check              fast
% 11.60/1.99  --demod_use_ground                      true
% 11.60/1.99  --sup_to_prop_solver                    passive
% 11.60/1.99  --sup_prop_simpl_new                    true
% 11.60/1.99  --sup_prop_simpl_given                  true
% 11.60/1.99  --sup_fun_splitting                     true
% 11.60/1.99  --sup_smt_interval                      50000
% 11.60/1.99  
% 11.60/1.99  ------ Superposition Simplification Setup
% 11.60/1.99  
% 11.60/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.60/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.60/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.60/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.60/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.60/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.60/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.60/1.99  --sup_immed_triv                        [TrivRules]
% 11.60/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.99  --sup_immed_bw_main                     []
% 11.60/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.60/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.60/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.99  --sup_input_bw                          []
% 11.60/1.99  
% 11.60/1.99  ------ Combination Options
% 11.60/1.99  
% 11.60/1.99  --comb_res_mult                         3
% 11.60/1.99  --comb_sup_mult                         2
% 11.60/1.99  --comb_inst_mult                        10
% 11.60/1.99  
% 11.60/1.99  ------ Debug Options
% 11.60/1.99  
% 11.60/1.99  --dbg_backtrace                         false
% 11.60/1.99  --dbg_dump_prop_clauses                 false
% 11.60/1.99  --dbg_dump_prop_clauses_file            -
% 11.60/1.99  --dbg_out_stat                          false
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  ------ Proving...
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  % SZS status Theorem for theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  fof(f1,axiom,(
% 11.60/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f42,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f1])).
% 11.60/1.99  
% 11.60/1.99  fof(f22,axiom,(
% 11.60/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f74,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f22])).
% 11.60/1.99  
% 11.60/1.99  fof(f13,axiom,(
% 11.60/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f58,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f13])).
% 11.60/1.99  
% 11.60/1.99  fof(f16,axiom,(
% 11.60/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f68,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f16])).
% 11.60/1.99  
% 11.60/1.99  fof(f17,axiom,(
% 11.60/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f69,plain,(
% 11.60/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f17])).
% 11.60/1.99  
% 11.60/1.99  fof(f18,axiom,(
% 11.60/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f70,plain,(
% 11.60/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f18])).
% 11.60/1.99  
% 11.60/1.99  fof(f19,axiom,(
% 11.60/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f71,plain,(
% 11.60/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f19])).
% 11.60/1.99  
% 11.60/1.99  fof(f20,axiom,(
% 11.60/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f72,plain,(
% 11.60/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f20])).
% 11.60/1.99  
% 11.60/1.99  fof(f21,axiom,(
% 11.60/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f73,plain,(
% 11.60/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f21])).
% 11.60/1.99  
% 11.60/1.99  fof(f76,plain,(
% 11.60/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f72,f73])).
% 11.60/1.99  
% 11.60/1.99  fof(f77,plain,(
% 11.60/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f71,f76])).
% 11.60/1.99  
% 11.60/1.99  fof(f78,plain,(
% 11.60/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f70,f77])).
% 11.60/1.99  
% 11.60/1.99  fof(f79,plain,(
% 11.60/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f69,f78])).
% 11.60/1.99  
% 11.60/1.99  fof(f80,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f68,f79])).
% 11.60/1.99  
% 11.60/1.99  fof(f91,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.60/1.99    inference(definition_unfolding,[],[f74,f58,f80])).
% 11.60/1.99  
% 11.60/1.99  fof(f11,axiom,(
% 11.60/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f56,plain,(
% 11.60/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f11])).
% 11.60/1.99  
% 11.60/1.99  fof(f2,axiom,(
% 11.60/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f43,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f2])).
% 11.60/1.99  
% 11.60/1.99  fof(f23,conjecture,(
% 11.60/1.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f24,negated_conjecture,(
% 11.60/1.99    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.60/1.99    inference(negated_conjecture,[],[f23])).
% 11.60/1.99  
% 11.60/1.99  fof(f29,plain,(
% 11.60/1.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 11.60/1.99    inference(ennf_transformation,[],[f24])).
% 11.60/1.99  
% 11.60/1.99  fof(f40,plain,(
% 11.60/1.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f41,plain,(
% 11.60/1.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.60/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f40])).
% 11.60/1.99  
% 11.60/1.99  fof(f75,plain,(
% 11.60/1.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.60/1.99    inference(cnf_transformation,[],[f41])).
% 11.60/1.99  
% 11.60/1.99  fof(f15,axiom,(
% 11.60/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f67,plain,(
% 11.60/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f15])).
% 11.60/1.99  
% 11.60/1.99  fof(f81,plain,(
% 11.60/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f67,f80])).
% 11.60/1.99  
% 11.60/1.99  fof(f92,plain,(
% 11.60/1.99    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 11.60/1.99    inference(definition_unfolding,[],[f75,f58,f81])).
% 11.60/1.99  
% 11.60/1.99  fof(f10,axiom,(
% 11.60/1.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f55,plain,(
% 11.60/1.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.60/1.99    inference(cnf_transformation,[],[f10])).
% 11.60/1.99  
% 11.60/1.99  fof(f12,axiom,(
% 11.60/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f57,plain,(
% 11.60/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.60/1.99    inference(cnf_transformation,[],[f12])).
% 11.60/1.99  
% 11.60/1.99  fof(f9,axiom,(
% 11.60/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f54,plain,(
% 11.60/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f9])).
% 11.60/1.99  
% 11.60/1.99  fof(f6,axiom,(
% 11.60/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f51,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f6])).
% 11.60/1.99  
% 11.60/1.99  fof(f82,plain,(
% 11.60/1.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.60/1.99    inference(definition_unfolding,[],[f54,f51])).
% 11.60/1.99  
% 11.60/1.99  fof(f7,axiom,(
% 11.60/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f27,plain,(
% 11.60/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.60/1.99    inference(ennf_transformation,[],[f7])).
% 11.60/1.99  
% 11.60/1.99  fof(f52,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f27])).
% 11.60/1.99  
% 11.60/1.99  fof(f8,axiom,(
% 11.60/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f53,plain,(
% 11.60/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f8])).
% 11.60/1.99  
% 11.60/1.99  fof(f4,axiom,(
% 11.60/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f25,plain,(
% 11.60/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.60/1.99    inference(rectify,[],[f4])).
% 11.60/1.99  
% 11.60/1.99  fof(f26,plain,(
% 11.60/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.60/1.99    inference(ennf_transformation,[],[f25])).
% 11.60/1.99  
% 11.60/1.99  fof(f31,plain,(
% 11.60/1.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f32,plain,(
% 11.60/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.60/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f31])).
% 11.60/1.99  
% 11.60/1.99  fof(f47,plain,(
% 11.60/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f32])).
% 11.60/1.99  
% 11.60/1.99  fof(f3,axiom,(
% 11.60/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f30,plain,(
% 11.60/1.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.60/1.99    inference(nnf_transformation,[],[f3])).
% 11.60/1.99  
% 11.60/1.99  fof(f45,plain,(
% 11.60/1.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.60/1.99    inference(cnf_transformation,[],[f30])).
% 11.60/1.99  
% 11.60/1.99  fof(f5,axiom,(
% 11.60/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f33,plain,(
% 11.60/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.60/1.99    inference(nnf_transformation,[],[f5])).
% 11.60/1.99  
% 11.60/1.99  fof(f34,plain,(
% 11.60/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.60/1.99    inference(flattening,[],[f33])).
% 11.60/1.99  
% 11.60/1.99  fof(f48,plain,(
% 11.60/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.60/1.99    inference(cnf_transformation,[],[f34])).
% 11.60/1.99  
% 11.60/1.99  fof(f94,plain,(
% 11.60/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.60/1.99    inference(equality_resolution,[],[f48])).
% 11.60/1.99  
% 11.60/1.99  fof(f50,plain,(
% 11.60/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f34])).
% 11.60/1.99  
% 11.60/1.99  fof(f14,axiom,(
% 11.60/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.60/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f28,plain,(
% 11.60/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.60/1.99    inference(ennf_transformation,[],[f14])).
% 11.60/1.99  
% 11.60/1.99  fof(f35,plain,(
% 11.60/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.60/1.99    inference(nnf_transformation,[],[f28])).
% 11.60/1.99  
% 11.60/1.99  fof(f36,plain,(
% 11.60/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.60/1.99    inference(flattening,[],[f35])).
% 11.60/1.99  
% 11.60/1.99  fof(f37,plain,(
% 11.60/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.60/1.99    inference(rectify,[],[f36])).
% 11.60/1.99  
% 11.60/1.99  fof(f38,plain,(
% 11.60/1.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f39,plain,(
% 11.60/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.60/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 11.60/1.99  
% 11.60/1.99  fof(f60,plain,(
% 11.60/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.60/1.99    inference(cnf_transformation,[],[f39])).
% 11.60/1.99  
% 11.60/1.99  fof(f89,plain,(
% 11.60/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 11.60/1.99    inference(definition_unfolding,[],[f60,f79])).
% 11.60/1.99  
% 11.60/1.99  fof(f99,plain,(
% 11.60/1.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 11.60/1.99    inference(equality_resolution,[],[f89])).
% 11.60/1.99  
% 11.60/1.99  fof(f100,plain,(
% 11.60/1.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 11.60/1.99    inference(equality_resolution,[],[f99])).
% 11.60/1.99  
% 11.60/1.99  fof(f59,plain,(
% 11.60/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 11.60/1.99    inference(cnf_transformation,[],[f39])).
% 11.60/1.99  
% 11.60/1.99  fof(f90,plain,(
% 11.60/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 11.60/1.99    inference(definition_unfolding,[],[f59,f79])).
% 11.60/1.99  
% 11.60/1.99  fof(f101,plain,(
% 11.60/1.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 11.60/1.99    inference(equality_resolution,[],[f90])).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1210,plain,
% 11.60/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.60/1.99      theory(equality) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2245,plain,
% 11.60/1.99      ( r2_hidden(X0,X1)
% 11.60/1.99      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
% 11.60/1.99      | X0 != X2
% 11.60/1.99      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1210]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36941,plain,
% 11.60/1.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 11.60/1.99      | r2_hidden(X3,k1_xboole_0)
% 11.60/1.99      | X3 != X0
% 11.60/1.99      | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_2245]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36952,plain,
% 11.60/1.99      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 11.60/1.99      | r2_hidden(sK2,k1_xboole_0)
% 11.60/1.99      | sK2 != sK2
% 11.60/1.99      | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_36941]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_0,plain,
% 11.60/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_23,plain,
% 11.60/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 11.60/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.60/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1,plain,
% 11.60/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1204,plain,
% 11.60/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 11.60/1.99      inference(theory_normalisation,[status(thm)],[c_23,c_13,c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2124,plain,
% 11.60/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_0,c_1204]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_24,negated_conjecture,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1203,negated_conjecture,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 11.60/1.99      inference(theory_normalisation,[status(thm)],[c_24,c_13,c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1842,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_0,c_1203]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2133,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1842,c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1953,plain,
% 11.60/1.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2139,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_2133,c_1953]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2687,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13,c_2139]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_14,plain,
% 11.60/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2688,plain,
% 11.60/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_14,c_2139]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2697,plain,
% 11.60/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_2688,c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2704,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_2697,c_2139]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2822,plain,
% 11.60/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2687,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1635,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4456,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_14,c_1635]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4513,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_4456,c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2715,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2704,c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4578,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = k5_xboole_0(sK3,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_4513,c_2715]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7174,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2704,c_4578]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7363,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_7174,c_7174]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1636,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4891,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2704,c_1636]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5231,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_4891,c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7397,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = X1 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_7363,c_2704,c_5231]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7606,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = X1 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1,c_7397]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7333,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(sK3,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_4513,c_7174]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2135,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13,c_14]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3080,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,sK3)) = k1_xboole_0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2715,c_2135]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5541,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3080,c_1636]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5555,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = X1 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_5541,c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_15512,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(sK3,X0))),X1)) = X1 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_7333,c_5555]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_15696,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = X1 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_15512,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_19097,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(X0,sK3) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_7606,c_15696]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_29647,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2822,c_19097]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2713,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2135,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2718,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_2713,c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3283,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,sK3)) = sK3 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1,c_2718]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4054,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3283,c_2822]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2707,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4060,plain,
% 11.60/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_4054,c_2707]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4565,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_4513,c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13647,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13,c_4565]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_28289,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13647,c_2822]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30031,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 11.60/1.99      inference(light_normalisation,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_29647,c_2704,c_4060,c_28289]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35441,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2124,c_30031]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_11,plain,
% 11.60/1.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1609,plain,
% 11.60/1.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2285,plain,
% 11.60/1.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_0,c_1609]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3770,plain,
% 11.60/1.99      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2697,c_2285]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_9,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1611,plain,
% 11.60/1.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_32928,plain,
% 11.60/1.99      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3770,c_1611]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4923,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X1,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1636,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5348,plain,
% 11.60/1.99      ( k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k5_xboole_0(sK3,sK3)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2822,c_4923]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5386,plain,
% 11.60/1.99      ( k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_5348,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3517,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(sK3,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3283,c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7601,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_4891,c_7397]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7698,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_7601,c_2704,c_5231]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_11014,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(k5_xboole_0(X1,sK3),X0)) = k5_xboole_0(sK3,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3517,c_7698]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_11106,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,sK3),X0)) = k5_xboole_0(sK3,X1) ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_11014,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_11970,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),X1),k5_xboole_0(sK3,X0)) = X1 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_11106,c_4513]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_22838,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),X1),sK3),X2),k5_xboole_0(X0,X1)) = X2 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2715,c_11970]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2714,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X0)) = k1_xboole_0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2704,c_2135]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3052,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2714,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3054,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_3052,c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3325,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = sK3 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2715,c_3054]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_6971,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),X1),sK3) = k5_xboole_0(X0,X1) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3325,c_4513]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_23335,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_22838,c_13,c_6971]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_34408,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_5386,c_23335]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_34856,plain,
% 11.60/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,sK3)) ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_34408,c_32928]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4896,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_3283,c_1636]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_34857,plain,
% 11.60/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_34856,c_14,c_4896]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2711,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1204,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7584,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))),k5_xboole_0(sK3,X0)) = k3_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2711,c_7397]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_7715,plain,
% 11.60/1.99      ( k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),k5_xboole_0(sK3,X0)) = k3_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_7584,c_2704,c_5231]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12168,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,X0)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_7715,c_7333]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12268,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,X0)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = X0 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_12168,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12972,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))),X0) = k5_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_12268,c_7174]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12989,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))),X0) = k3_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_12972,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13994,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X0) = k3_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2711,c_12989]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_27115,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X0) = k3_xboole_0(sK3,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_0,c_13994]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12167,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_7397,c_7333]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12269,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = X1 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_12167,c_2704,c_5231]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12446,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)),k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2822,c_12269]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12131,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2822,c_7333]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12277,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_12131,c_2704]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12577,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 11.60/1.99      inference(light_normalisation,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_12446,c_2704,c_12277]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35052,plain,
% 11.60/1.99      ( k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_27115,c_12577]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35053,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK3))) = k1_xboole_0 ),
% 11.60/1.99      inference(light_normalisation,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_35052,c_32928,c_34857]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35054,plain,
% 11.60/1.99      ( k5_xboole_0(sK3,k3_xboole_0(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_35053,c_1953]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_10,plain,
% 11.60/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1610,plain,
% 11.60/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_20531,plain,
% 11.60/1.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1610,c_1611]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35055,plain,
% 11.60/1.99      ( sK3 = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_35054,c_12,c_20531]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35458,plain,
% 11.60/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k1_xboole_0 ),
% 11.60/1.99      inference(light_normalisation,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_35441,c_32928,c_34857,c_35055]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_28262,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_13647,c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13825,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_4565,c_4565]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_28421,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_28262,c_13825]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35459,plain,
% 11.60/1.99      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_35458,c_1953,c_28421]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_28045,plain,
% 11.60/1.99      ( k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1204,c_13647]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35460,plain,
% 11.60/1.99      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_35459,c_28045]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35461,plain,
% 11.60/1.99      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_35460,c_20531]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35462,plain,
% 11.60/1.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_35461,c_12,c_1953]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_4,plain,
% 11.60/1.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1615,plain,
% 11.60/1.99      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 11.60/1.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36403,plain,
% 11.60/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 11.60/1.99      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_35462,c_1615]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36410,plain,
% 11.60/1.99      ( ~ r2_hidden(X0,k1_xboole_0) | ~ r1_xboole_0(X1,k1_xboole_0) ),
% 11.60/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_36403]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36412,plain,
% 11.60/1.99      ( ~ r2_hidden(sK2,k1_xboole_0) | ~ r1_xboole_0(sK2,k1_xboole_0) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_36410]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2,plain,
% 11.60/1.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1617,plain,
% 11.60/1.99      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 11.60/1.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36396,plain,
% 11.60/1.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_35462,c_1617]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36407,plain,
% 11.60/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.60/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_36396]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36409,plain,
% 11.60/1.99      ( r1_xboole_0(sK2,k1_xboole_0) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_36407]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1207,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1691,plain,
% 11.60/1.99      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1207]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1750,plain,
% 11.60/1.99      ( X0 != k1_xboole_0
% 11.60/1.99      | k1_xboole_0 = X0
% 11.60/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1691]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1830,plain,
% 11.60/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
% 11.60/1.99      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
% 11.60/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1750]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1831,plain,
% 11.60/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
% 11.60/1.99      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 11.60/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1830]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_8,plain,
% 11.60/1.99      ( r1_tarski(X0,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1726,plain,
% 11.60/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_6,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.60/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1681,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.60/1.99      | ~ r1_tarski(k1_xboole_0,X0)
% 11.60/1.99      | k1_xboole_0 = X0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1709,plain,
% 11.60/1.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.60/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1681]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_21,plain,
% 11.60/1.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 11.60/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30,plain,
% 11.60/1.99      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_21]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_22,plain,
% 11.60/1.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 11.60/1.99      | X0 = X1
% 11.60/1.99      | X0 = X2
% 11.60/1.99      | X0 = X3 ),
% 11.60/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_27,plain,
% 11.60/1.99      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 11.60/1.99      | sK2 = sK2 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(contradiction,plain,
% 11.60/1.99      ( $false ),
% 11.60/1.99      inference(minisat,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_36952,c_36412,c_36409,c_34857,c_1831,c_1726,c_1709,
% 11.60/1.99                 c_30,c_27]) ).
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  ------                               Statistics
% 11.60/1.99  
% 11.60/1.99  ------ General
% 11.60/1.99  
% 11.60/1.99  abstr_ref_over_cycles:                  0
% 11.60/1.99  abstr_ref_under_cycles:                 0
% 11.60/1.99  gc_basic_clause_elim:                   0
% 11.60/1.99  forced_gc_time:                         0
% 11.60/1.99  parsing_time:                           0.021
% 11.60/1.99  unif_index_cands_time:                  0.
% 11.60/1.99  unif_index_add_time:                    0.
% 11.60/1.99  orderings_time:                         0.
% 11.60/1.99  out_proof_time:                         0.012
% 11.60/1.99  total_time:                             1.172
% 11.60/1.99  num_of_symbols:                         43
% 11.60/1.99  num_of_terms:                           44521
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing
% 11.60/1.99  
% 11.60/1.99  num_of_splits:                          0
% 11.60/1.99  num_of_split_atoms:                     0
% 11.60/1.99  num_of_reused_defs:                     0
% 11.60/1.99  num_eq_ax_congr_red:                    27
% 11.60/1.99  num_of_sem_filtered_clauses:            1
% 11.60/1.99  num_of_subtypes:                        0
% 11.60/1.99  monotx_restored_types:                  0
% 11.60/1.99  sat_num_of_epr_types:                   0
% 11.60/1.99  sat_num_of_non_cyclic_types:            0
% 11.60/1.99  sat_guarded_non_collapsed_types:        0
% 11.60/1.99  num_pure_diseq_elim:                    0
% 11.60/1.99  simp_replaced_by:                       0
% 11.60/1.99  res_preprocessed:                       113
% 11.60/1.99  prep_upred:                             0
% 11.60/1.99  prep_unflattend:                        56
% 11.60/1.99  smt_new_axioms:                         0
% 11.60/1.99  pred_elim_cands:                        3
% 11.60/1.99  pred_elim:                              0
% 11.60/1.99  pred_elim_cl:                           0
% 11.60/1.99  pred_elim_cycles:                       4
% 11.60/1.99  merged_defs:                            8
% 11.60/1.99  merged_defs_ncl:                        0
% 11.60/1.99  bin_hyper_res:                          8
% 11.60/1.99  prep_cycles:                            4
% 11.60/1.99  pred_elim_time:                         0.017
% 11.60/1.99  splitting_time:                         0.
% 11.60/1.99  sem_filter_time:                        0.
% 11.60/1.99  monotx_time:                            0.001
% 11.60/1.99  subtype_inf_time:                       0.
% 11.60/1.99  
% 11.60/1.99  ------ Problem properties
% 11.60/1.99  
% 11.60/1.99  clauses:                                24
% 11.60/1.99  conjectures:                            1
% 11.60/1.99  epr:                                    3
% 11.60/1.99  horn:                                   21
% 11.60/1.99  ground:                                 1
% 11.60/1.99  unary:                                  13
% 11.60/1.99  binary:                                 5
% 11.60/1.99  lits:                                   44
% 11.60/1.99  lits_eq:                                24
% 11.60/1.99  fd_pure:                                0
% 11.60/1.99  fd_pseudo:                              0
% 11.60/1.99  fd_cond:                                0
% 11.60/1.99  fd_pseudo_cond:                         5
% 11.60/1.99  ac_symbols:                             1
% 11.60/1.99  
% 11.60/1.99  ------ Propositional Solver
% 11.60/1.99  
% 11.60/1.99  prop_solver_calls:                      31
% 11.60/1.99  prop_fast_solver_calls:                 852
% 11.60/1.99  smt_solver_calls:                       0
% 11.60/1.99  smt_fast_solver_calls:                  0
% 11.60/1.99  prop_num_of_clauses:                    8075
% 11.60/1.99  prop_preprocess_simplified:             11132
% 11.60/1.99  prop_fo_subsumed:                       1
% 11.60/1.99  prop_solver_time:                       0.
% 11.60/1.99  smt_solver_time:                        0.
% 11.60/1.99  smt_fast_solver_time:                   0.
% 11.60/1.99  prop_fast_solver_time:                  0.
% 11.60/1.99  prop_unsat_core_time:                   0.
% 11.60/1.99  
% 11.60/1.99  ------ QBF
% 11.60/1.99  
% 11.60/1.99  qbf_q_res:                              0
% 11.60/1.99  qbf_num_tautologies:                    0
% 11.60/1.99  qbf_prep_cycles:                        0
% 11.60/1.99  
% 11.60/1.99  ------ BMC1
% 11.60/1.99  
% 11.60/1.99  bmc1_current_bound:                     -1
% 11.60/1.99  bmc1_last_solved_bound:                 -1
% 11.60/1.99  bmc1_unsat_core_size:                   -1
% 11.60/1.99  bmc1_unsat_core_parents_size:           -1
% 11.60/1.99  bmc1_merge_next_fun:                    0
% 11.60/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.60/1.99  
% 11.60/1.99  ------ Instantiation
% 11.60/1.99  
% 11.60/1.99  inst_num_of_clauses:                    1382
% 11.60/1.99  inst_num_in_passive:                    81
% 11.60/1.99  inst_num_in_active:                     704
% 11.60/1.99  inst_num_in_unprocessed:                598
% 11.60/1.99  inst_num_of_loops:                      814
% 11.60/1.99  inst_num_of_learning_restarts:          0
% 11.60/1.99  inst_num_moves_active_passive:          104
% 11.60/1.99  inst_lit_activity:                      0
% 11.60/1.99  inst_lit_activity_moves:                0
% 11.60/1.99  inst_num_tautologies:                   0
% 11.60/1.99  inst_num_prop_implied:                  0
% 11.60/1.99  inst_num_existing_simplified:           0
% 11.60/1.99  inst_num_eq_res_simplified:             0
% 11.60/1.99  inst_num_child_elim:                    0
% 11.60/1.99  inst_num_of_dismatching_blockings:      1104
% 11.60/1.99  inst_num_of_non_proper_insts:           1431
% 11.60/1.99  inst_num_of_duplicates:                 0
% 11.60/1.99  inst_inst_num_from_inst_to_res:         0
% 11.60/1.99  inst_dismatching_checking_time:         0.
% 11.60/1.99  
% 11.60/1.99  ------ Resolution
% 11.60/1.99  
% 11.60/1.99  res_num_of_clauses:                     0
% 11.60/1.99  res_num_in_passive:                     0
% 11.60/1.99  res_num_in_active:                      0
% 11.60/1.99  res_num_of_loops:                       117
% 11.60/1.99  res_forward_subset_subsumed:            350
% 11.60/1.99  res_backward_subset_subsumed:           4
% 11.60/1.99  res_forward_subsumed:                   0
% 11.60/1.99  res_backward_subsumed:                  0
% 11.60/1.99  res_forward_subsumption_resolution:     2
% 11.60/1.99  res_backward_subsumption_resolution:    0
% 11.60/1.99  res_clause_to_clause_subsumption:       37791
% 11.60/1.99  res_orphan_elimination:                 0
% 11.60/1.99  res_tautology_del:                      159
% 11.60/1.99  res_num_eq_res_simplified:              0
% 11.60/1.99  res_num_sel_changes:                    0
% 11.60/1.99  res_moves_from_active_to_pass:          0
% 11.60/1.99  
% 11.60/1.99  ------ Superposition
% 11.60/1.99  
% 11.60/1.99  sup_time_total:                         0.
% 11.60/1.99  sup_time_generating:                    0.
% 11.60/1.99  sup_time_sim_full:                      0.
% 11.60/1.99  sup_time_sim_immed:                     0.
% 11.60/1.99  
% 11.60/1.99  sup_num_of_clauses:                     2340
% 11.60/1.99  sup_num_in_active:                      42
% 11.60/1.99  sup_num_in_passive:                     2298
% 11.60/1.99  sup_num_of_loops:                       162
% 11.60/1.99  sup_fw_superposition:                   10026
% 11.60/1.99  sup_bw_superposition:                   7286
% 11.60/1.99  sup_immediate_simplified:               6845
% 11.60/1.99  sup_given_eliminated:                   9
% 11.60/1.99  comparisons_done:                       0
% 11.60/1.99  comparisons_avoided:                    6
% 11.60/1.99  
% 11.60/1.99  ------ Simplifications
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  sim_fw_subset_subsumed:                 0
% 11.60/1.99  sim_bw_subset_subsumed:                 0
% 11.60/1.99  sim_fw_subsumed:                        661
% 11.60/1.99  sim_bw_subsumed:                        28
% 11.60/1.99  sim_fw_subsumption_res:                 0
% 11.60/1.99  sim_bw_subsumption_res:                 0
% 11.60/1.99  sim_tautology_del:                      1
% 11.60/1.99  sim_eq_tautology_del:                   2195
% 11.60/1.99  sim_eq_res_simp:                        0
% 11.60/1.99  sim_fw_demodulated:                     3135
% 11.60/1.99  sim_bw_demodulated:                     189
% 11.60/1.99  sim_light_normalised:                   3262
% 11.60/1.99  sim_joinable_taut:                      727
% 11.60/1.99  sim_joinable_simp:                      0
% 11.60/1.99  sim_ac_normalised:                      0
% 11.60/1.99  sim_smt_subsumption:                    0
% 11.60/1.99  
%------------------------------------------------------------------------------
