%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:20 EST 2020

% Result     : Theorem 19.43s
% Output     : CNFRefutation 19.43s
% Verified   : 
% Statistics : Number of formulae       :  144 (1594 expanded)
%              Number of clauses        :   59 ( 147 expanded)
%              Number of leaves         :   27 ( 499 expanded)
%              Depth                    :   22
%              Number of atoms          :  305 (2405 expanded)
%              Number of equality atoms :  193 (2217 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f27])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f79])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK4
        | k1_tarski(sK2) != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_xboole_0 != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_tarski(sK2) != sK3 )
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f40])).

fof(f70,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f78])).

fof(f93,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f70,f79,f81])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f66,f81,f81])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f79])).

fof(f73,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,
    ( k1_xboole_0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f73,f81])).

fof(f71,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f71,f81,f81])).

fof(f72,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f72,f81])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_686,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_678,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_684,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_85119,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_684])).

cnf(c_85862,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_85119])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_681,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_85875,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_85862,c_681])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_13,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_677,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5414,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_677])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_674,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6030,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5414,c_674])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_423,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_14,c_0])).

cnf(c_680,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_6253,plain,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_680])).

cnf(c_6367,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6030,c_6253])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_942,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_940,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_15,c_14])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_424,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_14,c_0])).

cnf(c_4,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_688,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_424,c_4,c_15])).

cnf(c_868,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_688,c_0])).

cnf(c_946,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_940,c_868])).

cnf(c_1118,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_942,c_946])).

cnf(c_1127,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1118,c_688])).

cnf(c_6368,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6367,c_1127])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_708,plain,
    ( ~ r1_tarski(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_713,plain,
    ( ~ r1_tarski(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_426,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_838,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_429,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_766,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_1007,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_2079,plain,
    ( r1_tarski(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(sK4,sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_2083,plain,
    ( r1_tarski(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_tarski(sK4,sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6141,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6030,c_21])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_718,plain,
    ( ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_723,plain,
    ( ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_5418,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5414])).

cnf(c_6149,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6141,c_21,c_20,c_723,c_5418])).

cnf(c_6371,plain,
    ( r1_tarski(sK4,sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6368])).

cnf(c_6421,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6368,c_21,c_20,c_19,c_713,c_723,c_838,c_2083,c_5418,c_6030,c_6371])).

cnf(c_6430,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_6421,c_22])).

cnf(c_86730,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_85875,c_6430])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86730,c_6149])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:49:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 19.43/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.43/2.98  
% 19.43/2.98  ------  iProver source info
% 19.43/2.98  
% 19.43/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.43/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.43/2.98  git: non_committed_changes: false
% 19.43/2.98  git: last_make_outside_of_git: false
% 19.43/2.98  
% 19.43/2.98  ------ 
% 19.43/2.98  
% 19.43/2.98  ------ Input Options
% 19.43/2.98  
% 19.43/2.98  --out_options                           all
% 19.43/2.98  --tptp_safe_out                         true
% 19.43/2.98  --problem_path                          ""
% 19.43/2.98  --include_path                          ""
% 19.43/2.98  --clausifier                            res/vclausify_rel
% 19.43/2.98  --clausifier_options                    ""
% 19.43/2.98  --stdin                                 false
% 19.43/2.98  --stats_out                             all
% 19.43/2.98  
% 19.43/2.98  ------ General Options
% 19.43/2.98  
% 19.43/2.98  --fof                                   false
% 19.43/2.98  --time_out_real                         305.
% 19.43/2.98  --time_out_virtual                      -1.
% 19.43/2.98  --symbol_type_check                     false
% 19.43/2.98  --clausify_out                          false
% 19.43/2.98  --sig_cnt_out                           false
% 19.43/2.98  --trig_cnt_out                          false
% 19.43/2.98  --trig_cnt_out_tolerance                1.
% 19.43/2.98  --trig_cnt_out_sk_spl                   false
% 19.43/2.98  --abstr_cl_out                          false
% 19.43/2.98  
% 19.43/2.98  ------ Global Options
% 19.43/2.98  
% 19.43/2.98  --schedule                              default
% 19.43/2.98  --add_important_lit                     false
% 19.43/2.98  --prop_solver_per_cl                    1000
% 19.43/2.98  --min_unsat_core                        false
% 19.43/2.98  --soft_assumptions                      false
% 19.43/2.98  --soft_lemma_size                       3
% 19.43/2.98  --prop_impl_unit_size                   0
% 19.43/2.98  --prop_impl_unit                        []
% 19.43/2.98  --share_sel_clauses                     true
% 19.43/2.98  --reset_solvers                         false
% 19.43/2.98  --bc_imp_inh                            [conj_cone]
% 19.43/2.98  --conj_cone_tolerance                   3.
% 19.43/2.98  --extra_neg_conj                        none
% 19.43/2.98  --large_theory_mode                     true
% 19.43/2.98  --prolific_symb_bound                   200
% 19.43/2.98  --lt_threshold                          2000
% 19.43/2.98  --clause_weak_htbl                      true
% 19.43/2.98  --gc_record_bc_elim                     false
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing Options
% 19.43/2.98  
% 19.43/2.98  --preprocessing_flag                    true
% 19.43/2.98  --time_out_prep_mult                    0.1
% 19.43/2.98  --splitting_mode                        input
% 19.43/2.98  --splitting_grd                         true
% 19.43/2.98  --splitting_cvd                         false
% 19.43/2.98  --splitting_cvd_svl                     false
% 19.43/2.98  --splitting_nvd                         32
% 19.43/2.98  --sub_typing                            true
% 19.43/2.98  --prep_gs_sim                           true
% 19.43/2.98  --prep_unflatten                        true
% 19.43/2.98  --prep_res_sim                          true
% 19.43/2.98  --prep_upred                            true
% 19.43/2.98  --prep_sem_filter                       exhaustive
% 19.43/2.98  --prep_sem_filter_out                   false
% 19.43/2.98  --pred_elim                             true
% 19.43/2.98  --res_sim_input                         true
% 19.43/2.98  --eq_ax_congr_red                       true
% 19.43/2.98  --pure_diseq_elim                       true
% 19.43/2.98  --brand_transform                       false
% 19.43/2.98  --non_eq_to_eq                          false
% 19.43/2.98  --prep_def_merge                        true
% 19.43/2.98  --prep_def_merge_prop_impl              false
% 19.43/2.98  --prep_def_merge_mbd                    true
% 19.43/2.98  --prep_def_merge_tr_red                 false
% 19.43/2.98  --prep_def_merge_tr_cl                  false
% 19.43/2.98  --smt_preprocessing                     true
% 19.43/2.98  --smt_ac_axioms                         fast
% 19.43/2.98  --preprocessed_out                      false
% 19.43/2.98  --preprocessed_stats                    false
% 19.43/2.98  
% 19.43/2.98  ------ Abstraction refinement Options
% 19.43/2.98  
% 19.43/2.98  --abstr_ref                             []
% 19.43/2.98  --abstr_ref_prep                        false
% 19.43/2.98  --abstr_ref_until_sat                   false
% 19.43/2.98  --abstr_ref_sig_restrict                funpre
% 19.43/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.43/2.98  --abstr_ref_under                       []
% 19.43/2.98  
% 19.43/2.98  ------ SAT Options
% 19.43/2.98  
% 19.43/2.98  --sat_mode                              false
% 19.43/2.98  --sat_fm_restart_options                ""
% 19.43/2.98  --sat_gr_def                            false
% 19.43/2.98  --sat_epr_types                         true
% 19.43/2.98  --sat_non_cyclic_types                  false
% 19.43/2.98  --sat_finite_models                     false
% 19.43/2.98  --sat_fm_lemmas                         false
% 19.43/2.98  --sat_fm_prep                           false
% 19.43/2.98  --sat_fm_uc_incr                        true
% 19.43/2.98  --sat_out_model                         small
% 19.43/2.98  --sat_out_clauses                       false
% 19.43/2.98  
% 19.43/2.98  ------ QBF Options
% 19.43/2.98  
% 19.43/2.98  --qbf_mode                              false
% 19.43/2.98  --qbf_elim_univ                         false
% 19.43/2.98  --qbf_dom_inst                          none
% 19.43/2.98  --qbf_dom_pre_inst                      false
% 19.43/2.98  --qbf_sk_in                             false
% 19.43/2.98  --qbf_pred_elim                         true
% 19.43/2.98  --qbf_split                             512
% 19.43/2.98  
% 19.43/2.98  ------ BMC1 Options
% 19.43/2.98  
% 19.43/2.98  --bmc1_incremental                      false
% 19.43/2.98  --bmc1_axioms                           reachable_all
% 19.43/2.98  --bmc1_min_bound                        0
% 19.43/2.98  --bmc1_max_bound                        -1
% 19.43/2.98  --bmc1_max_bound_default                -1
% 19.43/2.98  --bmc1_symbol_reachability              true
% 19.43/2.98  --bmc1_property_lemmas                  false
% 19.43/2.98  --bmc1_k_induction                      false
% 19.43/2.98  --bmc1_non_equiv_states                 false
% 19.43/2.98  --bmc1_deadlock                         false
% 19.43/2.98  --bmc1_ucm                              false
% 19.43/2.98  --bmc1_add_unsat_core                   none
% 19.43/2.98  --bmc1_unsat_core_children              false
% 19.43/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.43/2.98  --bmc1_out_stat                         full
% 19.43/2.98  --bmc1_ground_init                      false
% 19.43/2.98  --bmc1_pre_inst_next_state              false
% 19.43/2.98  --bmc1_pre_inst_state                   false
% 19.43/2.98  --bmc1_pre_inst_reach_state             false
% 19.43/2.98  --bmc1_out_unsat_core                   false
% 19.43/2.98  --bmc1_aig_witness_out                  false
% 19.43/2.98  --bmc1_verbose                          false
% 19.43/2.98  --bmc1_dump_clauses_tptp                false
% 19.43/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.43/2.98  --bmc1_dump_file                        -
% 19.43/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.43/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.43/2.98  --bmc1_ucm_extend_mode                  1
% 19.43/2.98  --bmc1_ucm_init_mode                    2
% 19.43/2.98  --bmc1_ucm_cone_mode                    none
% 19.43/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.43/2.98  --bmc1_ucm_relax_model                  4
% 19.43/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.43/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.43/2.98  --bmc1_ucm_layered_model                none
% 19.43/2.98  --bmc1_ucm_max_lemma_size               10
% 19.43/2.98  
% 19.43/2.98  ------ AIG Options
% 19.43/2.98  
% 19.43/2.98  --aig_mode                              false
% 19.43/2.98  
% 19.43/2.98  ------ Instantiation Options
% 19.43/2.98  
% 19.43/2.98  --instantiation_flag                    true
% 19.43/2.98  --inst_sos_flag                         true
% 19.43/2.98  --inst_sos_phase                        true
% 19.43/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel_side                     num_symb
% 19.43/2.98  --inst_solver_per_active                1400
% 19.43/2.98  --inst_solver_calls_frac                1.
% 19.43/2.98  --inst_passive_queue_type               priority_queues
% 19.43/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.43/2.98  --inst_passive_queues_freq              [25;2]
% 19.43/2.98  --inst_dismatching                      true
% 19.43/2.98  --inst_eager_unprocessed_to_passive     true
% 19.43/2.98  --inst_prop_sim_given                   true
% 19.43/2.98  --inst_prop_sim_new                     false
% 19.43/2.98  --inst_subs_new                         false
% 19.43/2.98  --inst_eq_res_simp                      false
% 19.43/2.98  --inst_subs_given                       false
% 19.43/2.98  --inst_orphan_elimination               true
% 19.43/2.98  --inst_learning_loop_flag               true
% 19.43/2.98  --inst_learning_start                   3000
% 19.43/2.98  --inst_learning_factor                  2
% 19.43/2.98  --inst_start_prop_sim_after_learn       3
% 19.43/2.98  --inst_sel_renew                        solver
% 19.43/2.98  --inst_lit_activity_flag                true
% 19.43/2.98  --inst_restr_to_given                   false
% 19.43/2.98  --inst_activity_threshold               500
% 19.43/2.98  --inst_out_proof                        true
% 19.43/2.98  
% 19.43/2.98  ------ Resolution Options
% 19.43/2.98  
% 19.43/2.98  --resolution_flag                       true
% 19.43/2.98  --res_lit_sel                           adaptive
% 19.43/2.98  --res_lit_sel_side                      none
% 19.43/2.98  --res_ordering                          kbo
% 19.43/2.98  --res_to_prop_solver                    active
% 19.43/2.98  --res_prop_simpl_new                    false
% 19.43/2.98  --res_prop_simpl_given                  true
% 19.43/2.98  --res_passive_queue_type                priority_queues
% 19.43/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.43/2.98  --res_passive_queues_freq               [15;5]
% 19.43/2.98  --res_forward_subs                      full
% 19.43/2.98  --res_backward_subs                     full
% 19.43/2.98  --res_forward_subs_resolution           true
% 19.43/2.98  --res_backward_subs_resolution          true
% 19.43/2.98  --res_orphan_elimination                true
% 19.43/2.98  --res_time_limit                        2.
% 19.43/2.98  --res_out_proof                         true
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Options
% 19.43/2.98  
% 19.43/2.98  --superposition_flag                    true
% 19.43/2.98  --sup_passive_queue_type                priority_queues
% 19.43/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.43/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.43/2.98  --demod_completeness_check              fast
% 19.43/2.98  --demod_use_ground                      true
% 19.43/2.98  --sup_to_prop_solver                    passive
% 19.43/2.98  --sup_prop_simpl_new                    true
% 19.43/2.98  --sup_prop_simpl_given                  true
% 19.43/2.98  --sup_fun_splitting                     true
% 19.43/2.98  --sup_smt_interval                      50000
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Simplification Setup
% 19.43/2.98  
% 19.43/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.43/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.43/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_immed_triv                        [TrivRules]
% 19.43/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_bw_main                     []
% 19.43/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.43/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_input_bw                          []
% 19.43/2.98  
% 19.43/2.98  ------ Combination Options
% 19.43/2.98  
% 19.43/2.98  --comb_res_mult                         3
% 19.43/2.98  --comb_sup_mult                         2
% 19.43/2.98  --comb_inst_mult                        10
% 19.43/2.98  
% 19.43/2.98  ------ Debug Options
% 19.43/2.98  
% 19.43/2.98  --dbg_backtrace                         false
% 19.43/2.98  --dbg_dump_prop_clauses                 false
% 19.43/2.98  --dbg_dump_prop_clauses_file            -
% 19.43/2.98  --dbg_out_stat                          false
% 19.43/2.98  ------ Parsing...
% 19.43/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.43/2.98  ------ Proving...
% 19.43/2.98  ------ Problem Properties 
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  clauses                                 23
% 19.43/2.98  conjectures                             4
% 19.43/2.98  EPR                                     4
% 19.43/2.98  Horn                                    19
% 19.43/2.98  unary                                   11
% 19.43/2.98  binary                                  9
% 19.43/2.98  lits                                    38
% 19.43/2.98  lits eq                                 16
% 19.43/2.98  fd_pure                                 0
% 19.43/2.98  fd_pseudo                               0
% 19.43/2.98  fd_cond                                 1
% 19.43/2.98  fd_pseudo_cond                          1
% 19.43/2.98  AC symbols                              1
% 19.43/2.98  
% 19.43/2.98  ------ Schedule dynamic 5 is on 
% 19.43/2.98  
% 19.43/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  ------ 
% 19.43/2.98  Current options:
% 19.43/2.98  ------ 
% 19.43/2.98  
% 19.43/2.98  ------ Input Options
% 19.43/2.98  
% 19.43/2.98  --out_options                           all
% 19.43/2.98  --tptp_safe_out                         true
% 19.43/2.98  --problem_path                          ""
% 19.43/2.98  --include_path                          ""
% 19.43/2.98  --clausifier                            res/vclausify_rel
% 19.43/2.98  --clausifier_options                    ""
% 19.43/2.98  --stdin                                 false
% 19.43/2.98  --stats_out                             all
% 19.43/2.98  
% 19.43/2.98  ------ General Options
% 19.43/2.98  
% 19.43/2.98  --fof                                   false
% 19.43/2.98  --time_out_real                         305.
% 19.43/2.98  --time_out_virtual                      -1.
% 19.43/2.98  --symbol_type_check                     false
% 19.43/2.98  --clausify_out                          false
% 19.43/2.98  --sig_cnt_out                           false
% 19.43/2.98  --trig_cnt_out                          false
% 19.43/2.98  --trig_cnt_out_tolerance                1.
% 19.43/2.98  --trig_cnt_out_sk_spl                   false
% 19.43/2.98  --abstr_cl_out                          false
% 19.43/2.98  
% 19.43/2.98  ------ Global Options
% 19.43/2.98  
% 19.43/2.98  --schedule                              default
% 19.43/2.98  --add_important_lit                     false
% 19.43/2.98  --prop_solver_per_cl                    1000
% 19.43/2.98  --min_unsat_core                        false
% 19.43/2.98  --soft_assumptions                      false
% 19.43/2.98  --soft_lemma_size                       3
% 19.43/2.98  --prop_impl_unit_size                   0
% 19.43/2.98  --prop_impl_unit                        []
% 19.43/2.98  --share_sel_clauses                     true
% 19.43/2.98  --reset_solvers                         false
% 19.43/2.98  --bc_imp_inh                            [conj_cone]
% 19.43/2.98  --conj_cone_tolerance                   3.
% 19.43/2.98  --extra_neg_conj                        none
% 19.43/2.98  --large_theory_mode                     true
% 19.43/2.98  --prolific_symb_bound                   200
% 19.43/2.98  --lt_threshold                          2000
% 19.43/2.98  --clause_weak_htbl                      true
% 19.43/2.98  --gc_record_bc_elim                     false
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing Options
% 19.43/2.98  
% 19.43/2.98  --preprocessing_flag                    true
% 19.43/2.98  --time_out_prep_mult                    0.1
% 19.43/2.98  --splitting_mode                        input
% 19.43/2.98  --splitting_grd                         true
% 19.43/2.98  --splitting_cvd                         false
% 19.43/2.98  --splitting_cvd_svl                     false
% 19.43/2.98  --splitting_nvd                         32
% 19.43/2.98  --sub_typing                            true
% 19.43/2.98  --prep_gs_sim                           true
% 19.43/2.98  --prep_unflatten                        true
% 19.43/2.98  --prep_res_sim                          true
% 19.43/2.98  --prep_upred                            true
% 19.43/2.98  --prep_sem_filter                       exhaustive
% 19.43/2.98  --prep_sem_filter_out                   false
% 19.43/2.98  --pred_elim                             true
% 19.43/2.98  --res_sim_input                         true
% 19.43/2.98  --eq_ax_congr_red                       true
% 19.43/2.98  --pure_diseq_elim                       true
% 19.43/2.98  --brand_transform                       false
% 19.43/2.98  --non_eq_to_eq                          false
% 19.43/2.98  --prep_def_merge                        true
% 19.43/2.98  --prep_def_merge_prop_impl              false
% 19.43/2.98  --prep_def_merge_mbd                    true
% 19.43/2.98  --prep_def_merge_tr_red                 false
% 19.43/2.98  --prep_def_merge_tr_cl                  false
% 19.43/2.98  --smt_preprocessing                     true
% 19.43/2.98  --smt_ac_axioms                         fast
% 19.43/2.98  --preprocessed_out                      false
% 19.43/2.98  --preprocessed_stats                    false
% 19.43/2.98  
% 19.43/2.98  ------ Abstraction refinement Options
% 19.43/2.98  
% 19.43/2.98  --abstr_ref                             []
% 19.43/2.98  --abstr_ref_prep                        false
% 19.43/2.98  --abstr_ref_until_sat                   false
% 19.43/2.98  --abstr_ref_sig_restrict                funpre
% 19.43/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.43/2.98  --abstr_ref_under                       []
% 19.43/2.98  
% 19.43/2.98  ------ SAT Options
% 19.43/2.98  
% 19.43/2.98  --sat_mode                              false
% 19.43/2.98  --sat_fm_restart_options                ""
% 19.43/2.98  --sat_gr_def                            false
% 19.43/2.98  --sat_epr_types                         true
% 19.43/2.98  --sat_non_cyclic_types                  false
% 19.43/2.98  --sat_finite_models                     false
% 19.43/2.98  --sat_fm_lemmas                         false
% 19.43/2.98  --sat_fm_prep                           false
% 19.43/2.98  --sat_fm_uc_incr                        true
% 19.43/2.98  --sat_out_model                         small
% 19.43/2.98  --sat_out_clauses                       false
% 19.43/2.98  
% 19.43/2.98  ------ QBF Options
% 19.43/2.98  
% 19.43/2.98  --qbf_mode                              false
% 19.43/2.98  --qbf_elim_univ                         false
% 19.43/2.98  --qbf_dom_inst                          none
% 19.43/2.98  --qbf_dom_pre_inst                      false
% 19.43/2.98  --qbf_sk_in                             false
% 19.43/2.98  --qbf_pred_elim                         true
% 19.43/2.98  --qbf_split                             512
% 19.43/2.98  
% 19.43/2.98  ------ BMC1 Options
% 19.43/2.98  
% 19.43/2.98  --bmc1_incremental                      false
% 19.43/2.98  --bmc1_axioms                           reachable_all
% 19.43/2.98  --bmc1_min_bound                        0
% 19.43/2.98  --bmc1_max_bound                        -1
% 19.43/2.98  --bmc1_max_bound_default                -1
% 19.43/2.98  --bmc1_symbol_reachability              true
% 19.43/2.98  --bmc1_property_lemmas                  false
% 19.43/2.98  --bmc1_k_induction                      false
% 19.43/2.98  --bmc1_non_equiv_states                 false
% 19.43/2.98  --bmc1_deadlock                         false
% 19.43/2.98  --bmc1_ucm                              false
% 19.43/2.98  --bmc1_add_unsat_core                   none
% 19.43/2.98  --bmc1_unsat_core_children              false
% 19.43/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.43/2.98  --bmc1_out_stat                         full
% 19.43/2.98  --bmc1_ground_init                      false
% 19.43/2.98  --bmc1_pre_inst_next_state              false
% 19.43/2.98  --bmc1_pre_inst_state                   false
% 19.43/2.98  --bmc1_pre_inst_reach_state             false
% 19.43/2.98  --bmc1_out_unsat_core                   false
% 19.43/2.98  --bmc1_aig_witness_out                  false
% 19.43/2.98  --bmc1_verbose                          false
% 19.43/2.98  --bmc1_dump_clauses_tptp                false
% 19.43/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.43/2.98  --bmc1_dump_file                        -
% 19.43/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.43/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.43/2.98  --bmc1_ucm_extend_mode                  1
% 19.43/2.98  --bmc1_ucm_init_mode                    2
% 19.43/2.98  --bmc1_ucm_cone_mode                    none
% 19.43/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.43/2.98  --bmc1_ucm_relax_model                  4
% 19.43/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.43/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.43/2.98  --bmc1_ucm_layered_model                none
% 19.43/2.98  --bmc1_ucm_max_lemma_size               10
% 19.43/2.98  
% 19.43/2.98  ------ AIG Options
% 19.43/2.98  
% 19.43/2.98  --aig_mode                              false
% 19.43/2.98  
% 19.43/2.98  ------ Instantiation Options
% 19.43/2.98  
% 19.43/2.98  --instantiation_flag                    true
% 19.43/2.98  --inst_sos_flag                         true
% 19.43/2.98  --inst_sos_phase                        true
% 19.43/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel_side                     none
% 19.43/2.98  --inst_solver_per_active                1400
% 19.43/2.98  --inst_solver_calls_frac                1.
% 19.43/2.98  --inst_passive_queue_type               priority_queues
% 19.43/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.43/2.98  --inst_passive_queues_freq              [25;2]
% 19.43/2.98  --inst_dismatching                      true
% 19.43/2.98  --inst_eager_unprocessed_to_passive     true
% 19.43/2.98  --inst_prop_sim_given                   true
% 19.43/2.98  --inst_prop_sim_new                     false
% 19.43/2.98  --inst_subs_new                         false
% 19.43/2.98  --inst_eq_res_simp                      false
% 19.43/2.98  --inst_subs_given                       false
% 19.43/2.98  --inst_orphan_elimination               true
% 19.43/2.98  --inst_learning_loop_flag               true
% 19.43/2.98  --inst_learning_start                   3000
% 19.43/2.98  --inst_learning_factor                  2
% 19.43/2.98  --inst_start_prop_sim_after_learn       3
% 19.43/2.98  --inst_sel_renew                        solver
% 19.43/2.98  --inst_lit_activity_flag                true
% 19.43/2.98  --inst_restr_to_given                   false
% 19.43/2.98  --inst_activity_threshold               500
% 19.43/2.98  --inst_out_proof                        true
% 19.43/2.98  
% 19.43/2.98  ------ Resolution Options
% 19.43/2.98  
% 19.43/2.98  --resolution_flag                       false
% 19.43/2.98  --res_lit_sel                           adaptive
% 19.43/2.98  --res_lit_sel_side                      none
% 19.43/2.98  --res_ordering                          kbo
% 19.43/2.98  --res_to_prop_solver                    active
% 19.43/2.98  --res_prop_simpl_new                    false
% 19.43/2.98  --res_prop_simpl_given                  true
% 19.43/2.98  --res_passive_queue_type                priority_queues
% 19.43/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.43/2.98  --res_passive_queues_freq               [15;5]
% 19.43/2.98  --res_forward_subs                      full
% 19.43/2.98  --res_backward_subs                     full
% 19.43/2.98  --res_forward_subs_resolution           true
% 19.43/2.98  --res_backward_subs_resolution          true
% 19.43/2.98  --res_orphan_elimination                true
% 19.43/2.98  --res_time_limit                        2.
% 19.43/2.98  --res_out_proof                         true
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Options
% 19.43/2.98  
% 19.43/2.98  --superposition_flag                    true
% 19.43/2.98  --sup_passive_queue_type                priority_queues
% 19.43/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.43/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.43/2.98  --demod_completeness_check              fast
% 19.43/2.98  --demod_use_ground                      true
% 19.43/2.98  --sup_to_prop_solver                    passive
% 19.43/2.98  --sup_prop_simpl_new                    true
% 19.43/2.98  --sup_prop_simpl_given                  true
% 19.43/2.98  --sup_fun_splitting                     true
% 19.43/2.98  --sup_smt_interval                      50000
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Simplification Setup
% 19.43/2.98  
% 19.43/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.43/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.43/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_immed_triv                        [TrivRules]
% 19.43/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_bw_main                     []
% 19.43/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.43/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_input_bw                          []
% 19.43/2.98  
% 19.43/2.98  ------ Combination Options
% 19.43/2.98  
% 19.43/2.98  --comb_res_mult                         3
% 19.43/2.98  --comb_sup_mult                         2
% 19.43/2.98  --comb_inst_mult                        10
% 19.43/2.98  
% 19.43/2.98  ------ Debug Options
% 19.43/2.98  
% 19.43/2.98  --dbg_backtrace                         false
% 19.43/2.98  --dbg_dump_prop_clauses                 false
% 19.43/2.98  --dbg_dump_prop_clauses_file            -
% 19.43/2.98  --dbg_out_stat                          false
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  ------ Proving...
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  % SZS status Theorem for theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  fof(f2,axiom,(
% 19.43/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f27,plain,(
% 19.43/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.43/2.98    inference(ennf_transformation,[],[f2])).
% 19.43/2.98  
% 19.43/2.98  fof(f32,plain,(
% 19.43/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.43/2.98    inference(nnf_transformation,[],[f27])).
% 19.43/2.98  
% 19.43/2.98  fof(f33,plain,(
% 19.43/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.43/2.98    inference(rectify,[],[f32])).
% 19.43/2.98  
% 19.43/2.98  fof(f34,plain,(
% 19.43/2.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.43/2.98    introduced(choice_axiom,[])).
% 19.43/2.98  
% 19.43/2.98  fof(f35,plain,(
% 19.43/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.43/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 19.43/2.98  
% 19.43/2.98  fof(f44,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f35])).
% 19.43/2.98  
% 19.43/2.98  fof(f8,axiom,(
% 19.43/2.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f30,plain,(
% 19.43/2.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 19.43/2.98    inference(ennf_transformation,[],[f8])).
% 19.43/2.98  
% 19.43/2.98  fof(f53,plain,(
% 19.43/2.98    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f30])).
% 19.43/2.98  
% 19.43/2.98  fof(f94,plain,(
% 19.43/2.98    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 19.43/2.98    inference(equality_resolution,[],[f53])).
% 19.43/2.98  
% 19.43/2.98  fof(f5,axiom,(
% 19.43/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f26,plain,(
% 19.43/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.43/2.98    inference(rectify,[],[f5])).
% 19.43/2.98  
% 19.43/2.98  fof(f28,plain,(
% 19.43/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.43/2.98    inference(ennf_transformation,[],[f26])).
% 19.43/2.98  
% 19.43/2.98  fof(f36,plain,(
% 19.43/2.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 19.43/2.98    introduced(choice_axiom,[])).
% 19.43/2.98  
% 19.43/2.98  fof(f37,plain,(
% 19.43/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.43/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f36])).
% 19.43/2.98  
% 19.43/2.98  fof(f50,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f37])).
% 19.43/2.98  
% 19.43/2.98  fof(f6,axiom,(
% 19.43/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f29,plain,(
% 19.43/2.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.43/2.98    inference(ennf_transformation,[],[f6])).
% 19.43/2.98  
% 19.43/2.98  fof(f51,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f29])).
% 19.43/2.98  
% 19.43/2.98  fof(f21,axiom,(
% 19.43/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f69,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.43/2.98    inference(cnf_transformation,[],[f21])).
% 19.43/2.98  
% 19.43/2.98  fof(f14,axiom,(
% 19.43/2.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f60,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f14])).
% 19.43/2.98  
% 19.43/2.98  fof(f15,axiom,(
% 19.43/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f61,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f15])).
% 19.43/2.98  
% 19.43/2.98  fof(f16,axiom,(
% 19.43/2.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f62,plain,(
% 19.43/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f16])).
% 19.43/2.98  
% 19.43/2.98  fof(f17,axiom,(
% 19.43/2.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f63,plain,(
% 19.43/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f17])).
% 19.43/2.98  
% 19.43/2.98  fof(f18,axiom,(
% 19.43/2.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f64,plain,(
% 19.43/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f18])).
% 19.43/2.98  
% 19.43/2.98  fof(f19,axiom,(
% 19.43/2.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f65,plain,(
% 19.43/2.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f19])).
% 19.43/2.98  
% 19.43/2.98  fof(f74,plain,(
% 19.43/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f64,f65])).
% 19.43/2.98  
% 19.43/2.98  fof(f75,plain,(
% 19.43/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f63,f74])).
% 19.43/2.98  
% 19.43/2.98  fof(f76,plain,(
% 19.43/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f62,f75])).
% 19.43/2.98  
% 19.43/2.98  fof(f77,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f61,f76])).
% 19.43/2.98  
% 19.43/2.98  fof(f78,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f60,f77])).
% 19.43/2.98  
% 19.43/2.98  fof(f79,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.43/2.98    inference(definition_unfolding,[],[f69,f78])).
% 19.43/2.98  
% 19.43/2.98  fof(f84,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f51,f79])).
% 19.43/2.98  
% 19.43/2.98  fof(f22,conjecture,(
% 19.43/2.98    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f23,negated_conjecture,(
% 19.43/2.98    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 19.43/2.98    inference(negated_conjecture,[],[f22])).
% 19.43/2.98  
% 19.43/2.98  fof(f31,plain,(
% 19.43/2.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 19.43/2.98    inference(ennf_transformation,[],[f23])).
% 19.43/2.98  
% 19.43/2.98  fof(f40,plain,(
% 19.43/2.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 19.43/2.98    introduced(choice_axiom,[])).
% 19.43/2.98  
% 19.43/2.98  fof(f41,plain,(
% 19.43/2.98    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 19.43/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f40])).
% 19.43/2.98  
% 19.43/2.98  fof(f70,plain,(
% 19.43/2.98    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 19.43/2.98    inference(cnf_transformation,[],[f41])).
% 19.43/2.98  
% 19.43/2.98  fof(f13,axiom,(
% 19.43/2.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f59,plain,(
% 19.43/2.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f13])).
% 19.43/2.98  
% 19.43/2.98  fof(f81,plain,(
% 19.43/2.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f59,f78])).
% 19.43/2.98  
% 19.43/2.98  fof(f93,plain,(
% 19.43/2.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 19.43/2.98    inference(definition_unfolding,[],[f70,f79,f81])).
% 19.43/2.98  
% 19.43/2.98  fof(f9,axiom,(
% 19.43/2.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f55,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.43/2.98    inference(cnf_transformation,[],[f9])).
% 19.43/2.98  
% 19.43/2.98  fof(f86,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.43/2.98    inference(definition_unfolding,[],[f55,f79])).
% 19.43/2.98  
% 19.43/2.98  fof(f20,axiom,(
% 19.43/2.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f38,plain,(
% 19.43/2.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.43/2.98    inference(nnf_transformation,[],[f20])).
% 19.43/2.98  
% 19.43/2.98  fof(f39,plain,(
% 19.43/2.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.43/2.98    inference(flattening,[],[f38])).
% 19.43/2.98  
% 19.43/2.98  fof(f66,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 19.43/2.98    inference(cnf_transformation,[],[f39])).
% 19.43/2.98  
% 19.43/2.98  fof(f89,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 19.43/2.98    inference(definition_unfolding,[],[f66,f81,f81])).
% 19.43/2.98  
% 19.43/2.98  fof(f7,axiom,(
% 19.43/2.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f52,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f7])).
% 19.43/2.98  
% 19.43/2.98  fof(f12,axiom,(
% 19.43/2.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f58,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f12])).
% 19.43/2.98  
% 19.43/2.98  fof(f80,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f58,f79])).
% 19.43/2.98  
% 19.43/2.98  fof(f85,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 19.43/2.98    inference(definition_unfolding,[],[f52,f80])).
% 19.43/2.98  
% 19.43/2.98  fof(f10,axiom,(
% 19.43/2.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f56,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f10])).
% 19.43/2.98  
% 19.43/2.98  fof(f1,axiom,(
% 19.43/2.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f42,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f1])).
% 19.43/2.98  
% 19.43/2.98  fof(f11,axiom,(
% 19.43/2.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f57,plain,(
% 19.43/2.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.43/2.98    inference(cnf_transformation,[],[f11])).
% 19.43/2.98  
% 19.43/2.98  fof(f4,axiom,(
% 19.43/2.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f25,plain,(
% 19.43/2.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 19.43/2.98    inference(rectify,[],[f4])).
% 19.43/2.98  
% 19.43/2.98  fof(f47,plain,(
% 19.43/2.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 19.43/2.98    inference(cnf_transformation,[],[f25])).
% 19.43/2.98  
% 19.43/2.98  fof(f83,plain,(
% 19.43/2.98    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 19.43/2.98    inference(definition_unfolding,[],[f47,f80])).
% 19.43/2.98  
% 19.43/2.98  fof(f3,axiom,(
% 19.43/2.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f24,plain,(
% 19.43/2.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 19.43/2.98    inference(rectify,[],[f3])).
% 19.43/2.98  
% 19.43/2.98  fof(f46,plain,(
% 19.43/2.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 19.43/2.98    inference(cnf_transformation,[],[f24])).
% 19.43/2.98  
% 19.43/2.98  fof(f82,plain,(
% 19.43/2.98    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 19.43/2.98    inference(definition_unfolding,[],[f46,f79])).
% 19.43/2.98  
% 19.43/2.98  fof(f73,plain,(
% 19.43/2.98    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 19.43/2.98    inference(cnf_transformation,[],[f41])).
% 19.43/2.98  
% 19.43/2.98  fof(f90,plain,(
% 19.43/2.98    k1_xboole_0 != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 19.43/2.98    inference(definition_unfolding,[],[f73,f81])).
% 19.43/2.98  
% 19.43/2.98  fof(f71,plain,(
% 19.43/2.98    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 19.43/2.98    inference(cnf_transformation,[],[f41])).
% 19.43/2.98  
% 19.43/2.98  fof(f92,plain,(
% 19.43/2.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 19.43/2.98    inference(definition_unfolding,[],[f71,f81,f81])).
% 19.43/2.98  
% 19.43/2.98  fof(f72,plain,(
% 19.43/2.98    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 19.43/2.98    inference(cnf_transformation,[],[f41])).
% 19.43/2.98  
% 19.43/2.98  fof(f91,plain,(
% 19.43/2.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 19.43/2.98    inference(definition_unfolding,[],[f72,f81])).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2,plain,
% 19.43/2.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.43/2.98      inference(cnf_transformation,[],[f44]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_686,plain,
% 19.43/2.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.43/2.98      | r1_tarski(X0,X1) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_12,plain,
% 19.43/2.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f94]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_678,plain,
% 19.43/2.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6,plain,
% 19.43/2.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f50]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_684,plain,
% 19.43/2.98      ( r1_xboole_0(X0,X1) != iProver_top
% 19.43/2.98      | r2_hidden(X2,X1) != iProver_top
% 19.43/2.98      | r2_hidden(X2,X0) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_85119,plain,
% 19.43/2.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_678,c_684]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_85862,plain,
% 19.43/2.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_686,c_85119]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_9,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,X1)
% 19.43/2.98      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 19.43/2.98      inference(cnf_transformation,[],[f84]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_681,plain,
% 19.43/2.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 19.43/2.98      | r1_tarski(X0,X1) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_85875,plain,
% 19.43/2.98      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_85862,c_681]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_22,negated_conjecture,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 19.43/2.98      inference(cnf_transformation,[],[f93]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_13,plain,
% 19.43/2.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 19.43/2.98      inference(cnf_transformation,[],[f86]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_677,plain,
% 19.43/2.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_5414,plain,
% 19.43/2.98      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_22,c_677]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_18,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 19.43/2.98      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 19.43/2.98      | k1_xboole_0 = X0 ),
% 19.43/2.98      inference(cnf_transformation,[],[f89]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_674,plain,
% 19.43/2.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 19.43/2.98      | k1_xboole_0 = X1
% 19.43/2.98      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6030,plain,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 19.43/2.98      | sK3 = k1_xboole_0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_5414,c_674]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_10,plain,
% 19.43/2.98      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f85]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_14,plain,
% 19.43/2.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.43/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_0,plain,
% 19.43/2.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f42]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_423,plain,
% 19.43/2.98      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 19.43/2.98      inference(theory_normalisation,[status(thm)],[c_10,c_14,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_680,plain,
% 19.43/2.98      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6253,plain,
% 19.43/2.98      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_22,c_680]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6367,plain,
% 19.43/2.98      ( sK3 = k1_xboole_0
% 19.43/2.98      | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),sK3) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_6030,c_6253]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_15,plain,
% 19.43/2.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.43/2.98      inference(cnf_transformation,[],[f57]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_942,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_940,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_15,c_14]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_5,plain,
% 19.43/2.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 19.43/2.98      inference(cnf_transformation,[],[f83]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_424,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 19.43/2.98      inference(theory_normalisation,[status(thm)],[c_5,c_14,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4,plain,
% 19.43/2.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 19.43/2.98      inference(cnf_transformation,[],[f82]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_688,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_424,c_4,c_15]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_868,plain,
% 19.43/2.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_688,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_946,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_940,c_868]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1118,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_942,c_946]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1127,plain,
% 19.43/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_1118,c_688]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6368,plain,
% 19.43/2.98      ( sK3 = k1_xboole_0 | r1_tarski(sK4,sK3) = iProver_top ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_6367,c_1127]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_19,negated_conjecture,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 19.43/2.98      | k1_xboole_0 != sK4 ),
% 19.43/2.98      inference(cnf_transformation,[],[f90]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_708,plain,
% 19.43/2.98      ( ~ r1_tarski(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 19.43/2.98      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK4
% 19.43/2.98      | k1_xboole_0 = sK4 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_18]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_713,plain,
% 19.43/2.98      ( ~ r1_tarski(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 19.43/2.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 19.43/2.98      | k1_xboole_0 = sK4 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_708]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_426,plain,( X0 = X0 ),theory(equality) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_838,plain,
% 19.43/2.98      ( sK4 = sK4 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_426]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_429,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.43/2.98      theory(equality) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_766,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,X1)
% 19.43/2.98      | r1_tarski(sK4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 19.43/2.98      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 19.43/2.98      | sK4 != X0 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_429]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1007,plain,
% 19.43/2.98      ( ~ r1_tarski(sK4,X0)
% 19.43/2.98      | r1_tarski(sK4,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 19.43/2.98      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
% 19.43/2.98      | sK4 != sK4 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_766]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2079,plain,
% 19.43/2.98      ( r1_tarski(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 19.43/2.98      | ~ r1_tarski(sK4,sK3)
% 19.43/2.98      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != sK3
% 19.43/2.98      | sK4 != sK4 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_1007]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2083,plain,
% 19.43/2.98      ( r1_tarski(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 19.43/2.98      | ~ r1_tarski(sK4,sK3)
% 19.43/2.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 19.43/2.98      | sK4 != sK4 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_2079]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_21,negated_conjecture,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 19.43/2.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 19.43/2.98      inference(cnf_transformation,[],[f92]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6141,plain,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 19.43/2.98      | sK3 = k1_xboole_0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_6030,c_21]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_20,negated_conjecture,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 19.43/2.98      | k1_xboole_0 != sK3 ),
% 19.43/2.98      inference(cnf_transformation,[],[f91]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_718,plain,
% 19.43/2.98      ( ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 19.43/2.98      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK3
% 19.43/2.98      | k1_xboole_0 = sK3 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_18]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_723,plain,
% 19.43/2.98      ( ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 19.43/2.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 19.43/2.98      | k1_xboole_0 = sK3 ),
% 19.43/2.98      inference(instantiation,[status(thm)],[c_718]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_5418,plain,
% 19.43/2.98      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 19.43/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_5414]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6149,plain,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 19.43/2.98      inference(global_propositional_subsumption,
% 19.43/2.98                [status(thm)],
% 19.43/2.98                [c_6141,c_21,c_20,c_723,c_5418]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6371,plain,
% 19.43/2.98      ( r1_tarski(sK4,sK3) | sK3 = k1_xboole_0 ),
% 19.43/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_6368]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6421,plain,
% 19.43/2.98      ( sK3 = k1_xboole_0 ),
% 19.43/2.98      inference(global_propositional_subsumption,
% 19.43/2.98                [status(thm)],
% 19.43/2.98                [c_6368,c_21,c_20,c_19,c_713,c_723,c_838,c_2083,c_5418,
% 19.43/2.98                 c_6030,c_6371]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6430,plain,
% 19.43/2.98      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_6421,c_22]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_86730,plain,
% 19.43/2.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_85875,c_6430]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(contradiction,plain,
% 19.43/2.98      ( $false ),
% 19.43/2.98      inference(minisat,[status(thm)],[c_86730,c_6149]) ).
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  ------                               Statistics
% 19.43/2.98  
% 19.43/2.98  ------ General
% 19.43/2.98  
% 19.43/2.98  abstr_ref_over_cycles:                  0
% 19.43/2.98  abstr_ref_under_cycles:                 0
% 19.43/2.98  gc_basic_clause_elim:                   0
% 19.43/2.98  forced_gc_time:                         0
% 19.43/2.98  parsing_time:                           0.009
% 19.43/2.98  unif_index_cands_time:                  0.
% 19.43/2.98  unif_index_add_time:                    0.
% 19.43/2.98  orderings_time:                         0.
% 19.43/2.98  out_proof_time:                         0.009
% 19.43/2.98  total_time:                             2.334
% 19.43/2.98  num_of_symbols:                         43
% 19.43/2.98  num_of_terms:                           209662
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing
% 19.43/2.98  
% 19.43/2.98  num_of_splits:                          0
% 19.43/2.98  num_of_split_atoms:                     0
% 19.43/2.98  num_of_reused_defs:                     0
% 19.43/2.98  num_eq_ax_congr_red:                    10
% 19.43/2.98  num_of_sem_filtered_clauses:            1
% 19.43/2.98  num_of_subtypes:                        0
% 19.43/2.98  monotx_restored_types:                  0
% 19.43/2.98  sat_num_of_epr_types:                   0
% 19.43/2.98  sat_num_of_non_cyclic_types:            0
% 19.43/2.98  sat_guarded_non_collapsed_types:        0
% 19.43/2.98  num_pure_diseq_elim:                    0
% 19.43/2.98  simp_replaced_by:                       0
% 19.43/2.98  res_preprocessed:                       86
% 19.43/2.98  prep_upred:                             0
% 19.43/2.98  prep_unflattend:                        36
% 19.43/2.98  smt_new_axioms:                         0
% 19.43/2.98  pred_elim_cands:                        3
% 19.43/2.98  pred_elim:                              0
% 19.43/2.98  pred_elim_cl:                           0
% 19.43/2.98  pred_elim_cycles:                       2
% 19.43/2.98  merged_defs:                            0
% 19.43/2.98  merged_defs_ncl:                        0
% 19.43/2.98  bin_hyper_res:                          0
% 19.43/2.98  prep_cycles:                            3
% 19.43/2.98  pred_elim_time:                         0.004
% 19.43/2.98  splitting_time:                         0.
% 19.43/2.98  sem_filter_time:                        0.
% 19.43/2.98  monotx_time:                            0.
% 19.43/2.98  subtype_inf_time:                       0.
% 19.43/2.98  
% 19.43/2.98  ------ Problem properties
% 19.43/2.98  
% 19.43/2.98  clauses:                                23
% 19.43/2.98  conjectures:                            4
% 19.43/2.98  epr:                                    4
% 19.43/2.98  horn:                                   19
% 19.43/2.98  ground:                                 5
% 19.43/2.98  unary:                                  11
% 19.43/2.98  binary:                                 9
% 19.43/2.98  lits:                                   38
% 19.43/2.98  lits_eq:                                16
% 19.43/2.98  fd_pure:                                0
% 19.43/2.98  fd_pseudo:                              0
% 19.43/2.98  fd_cond:                                1
% 19.43/2.98  fd_pseudo_cond:                         1
% 19.43/2.98  ac_symbols:                             1
% 19.43/2.98  
% 19.43/2.98  ------ Propositional Solver
% 19.43/2.98  
% 19.43/2.98  prop_solver_calls:                      30
% 19.43/2.98  prop_fast_solver_calls:                 656
% 19.43/2.98  smt_solver_calls:                       0
% 19.43/2.98  smt_fast_solver_calls:                  0
% 19.43/2.98  prop_num_of_clauses:                    8604
% 19.43/2.98  prop_preprocess_simplified:             14478
% 19.43/2.98  prop_fo_subsumed:                       6
% 19.43/2.98  prop_solver_time:                       0.
% 19.43/2.98  smt_solver_time:                        0.
% 19.43/2.98  smt_fast_solver_time:                   0.
% 19.43/2.98  prop_fast_solver_time:                  0.
% 19.43/2.98  prop_unsat_core_time:                   0.
% 19.43/2.98  
% 19.43/2.98  ------ QBF
% 19.43/2.98  
% 19.43/2.98  qbf_q_res:                              0
% 19.43/2.98  qbf_num_tautologies:                    0
% 19.43/2.98  qbf_prep_cycles:                        0
% 19.43/2.98  
% 19.43/2.98  ------ BMC1
% 19.43/2.98  
% 19.43/2.98  bmc1_current_bound:                     -1
% 19.43/2.98  bmc1_last_solved_bound:                 -1
% 19.43/2.98  bmc1_unsat_core_size:                   -1
% 19.43/2.98  bmc1_unsat_core_parents_size:           -1
% 19.43/2.98  bmc1_merge_next_fun:                    0
% 19.43/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.43/2.98  
% 19.43/2.98  ------ Instantiation
% 19.43/2.98  
% 19.43/2.98  inst_num_of_clauses:                    1669
% 19.43/2.98  inst_num_in_passive:                    975
% 19.43/2.98  inst_num_in_active:                     674
% 19.43/2.98  inst_num_in_unprocessed:                20
% 19.43/2.98  inst_num_of_loops:                      890
% 19.43/2.98  inst_num_of_learning_restarts:          0
% 19.43/2.98  inst_num_moves_active_passive:          212
% 19.43/2.98  inst_lit_activity:                      0
% 19.43/2.98  inst_lit_activity_moves:                0
% 19.43/2.98  inst_num_tautologies:                   0
% 19.43/2.98  inst_num_prop_implied:                  0
% 19.43/2.98  inst_num_existing_simplified:           0
% 19.43/2.98  inst_num_eq_res_simplified:             0
% 19.43/2.98  inst_num_child_elim:                    0
% 19.43/2.98  inst_num_of_dismatching_blockings:      371
% 19.43/2.98  inst_num_of_non_proper_insts:           1614
% 19.43/2.98  inst_num_of_duplicates:                 0
% 19.43/2.98  inst_inst_num_from_inst_to_res:         0
% 19.43/2.98  inst_dismatching_checking_time:         0.
% 19.43/2.98  
% 19.43/2.98  ------ Resolution
% 19.43/2.98  
% 19.43/2.98  res_num_of_clauses:                     0
% 19.43/2.98  res_num_in_passive:                     0
% 19.43/2.98  res_num_in_active:                      0
% 19.43/2.98  res_num_of_loops:                       89
% 19.43/2.98  res_forward_subset_subsumed:            156
% 19.43/2.98  res_backward_subset_subsumed:           0
% 19.43/2.98  res_forward_subsumed:                   1
% 19.43/2.98  res_backward_subsumed:                  0
% 19.43/2.98  res_forward_subsumption_resolution:     0
% 19.43/2.98  res_backward_subsumption_resolution:    0
% 19.43/2.98  res_clause_to_clause_subsumption:       246434
% 19.43/2.98  res_orphan_elimination:                 0
% 19.43/2.98  res_tautology_del:                      184
% 19.43/2.98  res_num_eq_res_simplified:              0
% 19.43/2.98  res_num_sel_changes:                    0
% 19.43/2.98  res_moves_from_active_to_pass:          0
% 19.43/2.98  
% 19.43/2.98  ------ Superposition
% 19.43/2.98  
% 19.43/2.98  sup_time_total:                         0.
% 19.43/2.98  sup_time_generating:                    0.
% 19.43/2.98  sup_time_sim_full:                      0.
% 19.43/2.98  sup_time_sim_immed:                     0.
% 19.43/2.98  
% 19.43/2.98  sup_num_of_clauses:                     3134
% 19.43/2.98  sup_num_in_active:                      144
% 19.43/2.98  sup_num_in_passive:                     2990
% 19.43/2.98  sup_num_of_loops:                       176
% 19.43/2.98  sup_fw_superposition:                   26316
% 19.43/2.98  sup_bw_superposition:                   15974
% 19.43/2.98  sup_immediate_simplified:               24560
% 19.43/2.98  sup_given_eliminated:                   2
% 19.43/2.98  comparisons_done:                       0
% 19.43/2.98  comparisons_avoided:                    3
% 19.43/2.98  
% 19.43/2.98  ------ Simplifications
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  sim_fw_subset_subsumed:                 1
% 19.43/2.98  sim_bw_subset_subsumed:                 5
% 19.43/2.98  sim_fw_subsumed:                        640
% 19.43/2.98  sim_bw_subsumed:                        10
% 19.43/2.98  sim_fw_subsumption_res:                 0
% 19.43/2.98  sim_bw_subsumption_res:                 0
% 19.43/2.98  sim_tautology_del:                      1
% 19.43/2.98  sim_eq_tautology_del:                   2284
% 19.43/2.98  sim_eq_res_simp:                        0
% 19.43/2.98  sim_fw_demodulated:                     25965
% 19.43/2.98  sim_bw_demodulated:                     123
% 19.43/2.98  sim_light_normalised:                   7192
% 19.43/2.98  sim_joinable_taut:                      1144
% 19.43/2.98  sim_joinable_simp:                      0
% 19.43/2.98  sim_ac_normalised:                      0
% 19.43/2.98  sim_smt_subsumption:                    0
% 19.43/2.98  
%------------------------------------------------------------------------------
