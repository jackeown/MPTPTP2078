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
% DateTime   : Thu Dec  3 11:35:26 EST 2020

% Result     : Theorem 23.70s
% Output     : CNFRefutation 23.70s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 654 expanded)
%              Number of clauses        :   44 (  79 expanded)
%              Number of leaves         :   25 ( 206 expanded)
%              Depth                    :   18
%              Number of atoms          :  286 ( 836 expanded)
%              Number of equality atoms :  185 ( 717 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f79])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f79,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f65,f80,f71,f79])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f66,f79])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f64,f80,f71,f82])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X3,X1,X0) ),
    inference(definition_unfolding,[],[f63,f77,f77])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK2,sK4)
      & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_hidden(sK2,sK4)
    & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f39])).

fof(f74,plain,(
    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f98,plain,(
    k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_tarski(k5_enumset1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f74,f81,f79,f79])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f81])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
    inference(flattening,[],[f34])).

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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f78])).

fof(f101,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f102,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f101])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f43,f81])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f80])).

fof(f75,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1273,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_23,c_0])).

cnf(c_22,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_tarski(k5_enumset1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_243,negated_conjecture,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_25,c_12,c_1])).

cnf(c_1149,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_22,c_243])).

cnf(c_62583,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1273,c_1149])).

cnf(c_63166,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1273,c_62583])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_244,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_12,c_1])).

cnf(c_514,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_64548,plain,
    ( r1_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_63166,c_514])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_517,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_71907,plain,
    ( r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_64548,c_517])).

cnf(c_71909,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71907])).

cnf(c_19,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_45207,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_45208,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45207])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_245,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_12,c_1])).

cnf(c_518,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_29529,plain,
    ( r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_518])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1038,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_1578,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),X0)) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_1149,c_12])).

cnf(c_2141,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0))) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_12,c_1578])).

cnf(c_14126,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0))) = k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1038,c_2141])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_248,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_3,c_12,c_1])).

cnf(c_2,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_522,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_248,c_2,c_13])).

cnf(c_540,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_2706,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13,c_540])).

cnf(c_2756,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2706,c_522])).

cnf(c_14189,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) = k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_14126,c_522,c_2756])).

cnf(c_29598,plain,
    ( r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29529,c_14189])).

cnf(c_29657,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_29598])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71909,c_45208,c_29657,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:20:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.70/3.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.70/3.47  
% 23.70/3.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.70/3.47  
% 23.70/3.47  ------  iProver source info
% 23.70/3.47  
% 23.70/3.47  git: date: 2020-06-30 10:37:57 +0100
% 23.70/3.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.70/3.47  git: non_committed_changes: false
% 23.70/3.47  git: last_make_outside_of_git: false
% 23.70/3.47  
% 23.70/3.47  ------ 
% 23.70/3.47  
% 23.70/3.47  ------ Input Options
% 23.70/3.47  
% 23.70/3.47  --out_options                           all
% 23.70/3.47  --tptp_safe_out                         true
% 23.70/3.47  --problem_path                          ""
% 23.70/3.47  --include_path                          ""
% 23.70/3.47  --clausifier                            res/vclausify_rel
% 23.70/3.47  --clausifier_options                    ""
% 23.70/3.47  --stdin                                 false
% 23.70/3.47  --stats_out                             all
% 23.70/3.47  
% 23.70/3.47  ------ General Options
% 23.70/3.47  
% 23.70/3.47  --fof                                   false
% 23.70/3.47  --time_out_real                         305.
% 23.70/3.47  --time_out_virtual                      -1.
% 23.70/3.47  --symbol_type_check                     false
% 23.70/3.47  --clausify_out                          false
% 23.70/3.47  --sig_cnt_out                           false
% 23.70/3.47  --trig_cnt_out                          false
% 23.70/3.47  --trig_cnt_out_tolerance                1.
% 23.70/3.47  --trig_cnt_out_sk_spl                   false
% 23.70/3.47  --abstr_cl_out                          false
% 23.70/3.47  
% 23.70/3.47  ------ Global Options
% 23.70/3.47  
% 23.70/3.47  --schedule                              default
% 23.70/3.47  --add_important_lit                     false
% 23.70/3.47  --prop_solver_per_cl                    1000
% 23.70/3.47  --min_unsat_core                        false
% 23.70/3.47  --soft_assumptions                      false
% 23.70/3.47  --soft_lemma_size                       3
% 23.70/3.47  --prop_impl_unit_size                   0
% 23.70/3.47  --prop_impl_unit                        []
% 23.70/3.47  --share_sel_clauses                     true
% 23.70/3.47  --reset_solvers                         false
% 23.70/3.47  --bc_imp_inh                            [conj_cone]
% 23.70/3.47  --conj_cone_tolerance                   3.
% 23.70/3.47  --extra_neg_conj                        none
% 23.70/3.47  --large_theory_mode                     true
% 23.70/3.47  --prolific_symb_bound                   200
% 23.70/3.47  --lt_threshold                          2000
% 23.70/3.47  --clause_weak_htbl                      true
% 23.70/3.47  --gc_record_bc_elim                     false
% 23.70/3.47  
% 23.70/3.47  ------ Preprocessing Options
% 23.70/3.47  
% 23.70/3.47  --preprocessing_flag                    true
% 23.70/3.47  --time_out_prep_mult                    0.1
% 23.70/3.47  --splitting_mode                        input
% 23.70/3.47  --splitting_grd                         true
% 23.70/3.47  --splitting_cvd                         false
% 23.70/3.47  --splitting_cvd_svl                     false
% 23.70/3.47  --splitting_nvd                         32
% 23.70/3.47  --sub_typing                            true
% 23.70/3.47  --prep_gs_sim                           true
% 23.70/3.47  --prep_unflatten                        true
% 23.70/3.47  --prep_res_sim                          true
% 23.70/3.47  --prep_upred                            true
% 23.70/3.47  --prep_sem_filter                       exhaustive
% 23.70/3.47  --prep_sem_filter_out                   false
% 23.70/3.47  --pred_elim                             true
% 23.70/3.47  --res_sim_input                         true
% 23.70/3.47  --eq_ax_congr_red                       true
% 23.70/3.47  --pure_diseq_elim                       true
% 23.70/3.47  --brand_transform                       false
% 23.70/3.47  --non_eq_to_eq                          false
% 23.70/3.47  --prep_def_merge                        true
% 23.70/3.47  --prep_def_merge_prop_impl              false
% 23.70/3.47  --prep_def_merge_mbd                    true
% 23.70/3.47  --prep_def_merge_tr_red                 false
% 23.70/3.47  --prep_def_merge_tr_cl                  false
% 23.70/3.47  --smt_preprocessing                     true
% 23.70/3.47  --smt_ac_axioms                         fast
% 23.70/3.47  --preprocessed_out                      false
% 23.70/3.47  --preprocessed_stats                    false
% 23.70/3.47  
% 23.70/3.47  ------ Abstraction refinement Options
% 23.70/3.47  
% 23.70/3.47  --abstr_ref                             []
% 23.70/3.47  --abstr_ref_prep                        false
% 23.70/3.47  --abstr_ref_until_sat                   false
% 23.70/3.47  --abstr_ref_sig_restrict                funpre
% 23.70/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.70/3.47  --abstr_ref_under                       []
% 23.70/3.47  
% 23.70/3.47  ------ SAT Options
% 23.70/3.47  
% 23.70/3.47  --sat_mode                              false
% 23.70/3.47  --sat_fm_restart_options                ""
% 23.70/3.47  --sat_gr_def                            false
% 23.70/3.47  --sat_epr_types                         true
% 23.70/3.47  --sat_non_cyclic_types                  false
% 23.70/3.47  --sat_finite_models                     false
% 23.70/3.47  --sat_fm_lemmas                         false
% 23.70/3.47  --sat_fm_prep                           false
% 23.70/3.47  --sat_fm_uc_incr                        true
% 23.70/3.47  --sat_out_model                         small
% 23.70/3.47  --sat_out_clauses                       false
% 23.70/3.47  
% 23.70/3.47  ------ QBF Options
% 23.70/3.47  
% 23.70/3.47  --qbf_mode                              false
% 23.70/3.47  --qbf_elim_univ                         false
% 23.70/3.47  --qbf_dom_inst                          none
% 23.70/3.47  --qbf_dom_pre_inst                      false
% 23.70/3.47  --qbf_sk_in                             false
% 23.70/3.47  --qbf_pred_elim                         true
% 23.70/3.47  --qbf_split                             512
% 23.70/3.47  
% 23.70/3.47  ------ BMC1 Options
% 23.70/3.47  
% 23.70/3.47  --bmc1_incremental                      false
% 23.70/3.47  --bmc1_axioms                           reachable_all
% 23.70/3.47  --bmc1_min_bound                        0
% 23.70/3.47  --bmc1_max_bound                        -1
% 23.70/3.47  --bmc1_max_bound_default                -1
% 23.70/3.47  --bmc1_symbol_reachability              true
% 23.70/3.47  --bmc1_property_lemmas                  false
% 23.70/3.47  --bmc1_k_induction                      false
% 23.70/3.47  --bmc1_non_equiv_states                 false
% 23.70/3.47  --bmc1_deadlock                         false
% 23.70/3.47  --bmc1_ucm                              false
% 23.70/3.47  --bmc1_add_unsat_core                   none
% 23.70/3.47  --bmc1_unsat_core_children              false
% 23.70/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.70/3.47  --bmc1_out_stat                         full
% 23.70/3.47  --bmc1_ground_init                      false
% 23.70/3.47  --bmc1_pre_inst_next_state              false
% 23.70/3.47  --bmc1_pre_inst_state                   false
% 23.70/3.47  --bmc1_pre_inst_reach_state             false
% 23.70/3.47  --bmc1_out_unsat_core                   false
% 23.70/3.47  --bmc1_aig_witness_out                  false
% 23.70/3.47  --bmc1_verbose                          false
% 23.70/3.47  --bmc1_dump_clauses_tptp                false
% 23.70/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.70/3.47  --bmc1_dump_file                        -
% 23.70/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.70/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.70/3.47  --bmc1_ucm_extend_mode                  1
% 23.70/3.47  --bmc1_ucm_init_mode                    2
% 23.70/3.47  --bmc1_ucm_cone_mode                    none
% 23.70/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.70/3.47  --bmc1_ucm_relax_model                  4
% 23.70/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.70/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.70/3.47  --bmc1_ucm_layered_model                none
% 23.70/3.47  --bmc1_ucm_max_lemma_size               10
% 23.70/3.47  
% 23.70/3.47  ------ AIG Options
% 23.70/3.47  
% 23.70/3.47  --aig_mode                              false
% 23.70/3.47  
% 23.70/3.47  ------ Instantiation Options
% 23.70/3.47  
% 23.70/3.47  --instantiation_flag                    true
% 23.70/3.47  --inst_sos_flag                         true
% 23.70/3.47  --inst_sos_phase                        true
% 23.70/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.70/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.70/3.47  --inst_lit_sel_side                     num_symb
% 23.70/3.47  --inst_solver_per_active                1400
% 23.70/3.47  --inst_solver_calls_frac                1.
% 23.70/3.47  --inst_passive_queue_type               priority_queues
% 23.70/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.70/3.47  --inst_passive_queues_freq              [25;2]
% 23.70/3.47  --inst_dismatching                      true
% 23.70/3.47  --inst_eager_unprocessed_to_passive     true
% 23.70/3.47  --inst_prop_sim_given                   true
% 23.70/3.47  --inst_prop_sim_new                     false
% 23.70/3.47  --inst_subs_new                         false
% 23.70/3.47  --inst_eq_res_simp                      false
% 23.70/3.47  --inst_subs_given                       false
% 23.70/3.47  --inst_orphan_elimination               true
% 23.70/3.47  --inst_learning_loop_flag               true
% 23.70/3.47  --inst_learning_start                   3000
% 23.70/3.47  --inst_learning_factor                  2
% 23.70/3.47  --inst_start_prop_sim_after_learn       3
% 23.70/3.47  --inst_sel_renew                        solver
% 23.70/3.47  --inst_lit_activity_flag                true
% 23.70/3.47  --inst_restr_to_given                   false
% 23.70/3.47  --inst_activity_threshold               500
% 23.70/3.47  --inst_out_proof                        true
% 23.70/3.47  
% 23.70/3.47  ------ Resolution Options
% 23.70/3.47  
% 23.70/3.47  --resolution_flag                       true
% 23.70/3.47  --res_lit_sel                           adaptive
% 23.70/3.47  --res_lit_sel_side                      none
% 23.70/3.47  --res_ordering                          kbo
% 23.70/3.47  --res_to_prop_solver                    active
% 23.70/3.47  --res_prop_simpl_new                    false
% 23.70/3.47  --res_prop_simpl_given                  true
% 23.70/3.47  --res_passive_queue_type                priority_queues
% 23.70/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.70/3.47  --res_passive_queues_freq               [15;5]
% 23.70/3.47  --res_forward_subs                      full
% 23.70/3.47  --res_backward_subs                     full
% 23.70/3.47  --res_forward_subs_resolution           true
% 23.70/3.47  --res_backward_subs_resolution          true
% 23.70/3.47  --res_orphan_elimination                true
% 23.70/3.47  --res_time_limit                        2.
% 23.70/3.47  --res_out_proof                         true
% 23.70/3.47  
% 23.70/3.47  ------ Superposition Options
% 23.70/3.47  
% 23.70/3.47  --superposition_flag                    true
% 23.70/3.47  --sup_passive_queue_type                priority_queues
% 23.70/3.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.70/3.47  --sup_passive_queues_freq               [8;1;4]
% 23.70/3.47  --demod_completeness_check              fast
% 23.70/3.47  --demod_use_ground                      true
% 23.70/3.47  --sup_to_prop_solver                    passive
% 23.70/3.47  --sup_prop_simpl_new                    true
% 23.70/3.47  --sup_prop_simpl_given                  true
% 23.70/3.47  --sup_fun_splitting                     true
% 23.70/3.47  --sup_smt_interval                      50000
% 23.70/3.47  
% 23.70/3.47  ------ Superposition Simplification Setup
% 23.70/3.47  
% 23.70/3.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.70/3.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.70/3.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.70/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.70/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.70/3.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.70/3.47  --sup_immed_triv                        [TrivRules]
% 23.70/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.47  --sup_immed_bw_main                     []
% 23.70/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.70/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.70/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.47  --sup_input_bw                          []
% 23.70/3.47  
% 23.70/3.47  ------ Combination Options
% 23.70/3.47  
% 23.70/3.47  --comb_res_mult                         3
% 23.70/3.47  --comb_sup_mult                         2
% 23.70/3.47  --comb_inst_mult                        10
% 23.70/3.47  
% 23.70/3.47  ------ Debug Options
% 23.70/3.47  
% 23.70/3.47  --dbg_backtrace                         false
% 23.70/3.47  --dbg_dump_prop_clauses                 false
% 23.70/3.47  --dbg_dump_prop_clauses_file            -
% 23.70/3.47  --dbg_out_stat                          false
% 23.70/3.47  ------ Parsing...
% 23.70/3.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.70/3.47  
% 23.70/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.70/3.47  
% 23.70/3.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.70/3.47  
% 23.70/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.70/3.47  ------ Proving...
% 23.70/3.47  ------ Problem Properties 
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  clauses                                 26
% 23.70/3.47  conjectures                             2
% 23.70/3.47  EPR                                     2
% 23.70/3.47  Horn                                    19
% 23.70/3.47  unary                                   14
% 23.70/3.47  binary                                  2
% 23.70/3.47  lits                                    51
% 23.70/3.47  lits eq                                 22
% 23.70/3.47  fd_pure                                 0
% 23.70/3.47  fd_pseudo                               0
% 23.70/3.47  fd_cond                                 0
% 23.70/3.47  fd_pseudo_cond                          4
% 23.70/3.47  AC symbols                              1
% 23.70/3.47  
% 23.70/3.47  ------ Schedule dynamic 5 is on 
% 23.70/3.47  
% 23.70/3.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  ------ 
% 23.70/3.47  Current options:
% 23.70/3.47  ------ 
% 23.70/3.47  
% 23.70/3.47  ------ Input Options
% 23.70/3.47  
% 23.70/3.47  --out_options                           all
% 23.70/3.47  --tptp_safe_out                         true
% 23.70/3.47  --problem_path                          ""
% 23.70/3.47  --include_path                          ""
% 23.70/3.47  --clausifier                            res/vclausify_rel
% 23.70/3.47  --clausifier_options                    ""
% 23.70/3.47  --stdin                                 false
% 23.70/3.47  --stats_out                             all
% 23.70/3.47  
% 23.70/3.47  ------ General Options
% 23.70/3.47  
% 23.70/3.47  --fof                                   false
% 23.70/3.47  --time_out_real                         305.
% 23.70/3.47  --time_out_virtual                      -1.
% 23.70/3.47  --symbol_type_check                     false
% 23.70/3.47  --clausify_out                          false
% 23.70/3.47  --sig_cnt_out                           false
% 23.70/3.47  --trig_cnt_out                          false
% 23.70/3.47  --trig_cnt_out_tolerance                1.
% 23.70/3.47  --trig_cnt_out_sk_spl                   false
% 23.70/3.47  --abstr_cl_out                          false
% 23.70/3.47  
% 23.70/3.47  ------ Global Options
% 23.70/3.47  
% 23.70/3.47  --schedule                              default
% 23.70/3.47  --add_important_lit                     false
% 23.70/3.47  --prop_solver_per_cl                    1000
% 23.70/3.47  --min_unsat_core                        false
% 23.70/3.47  --soft_assumptions                      false
% 23.70/3.47  --soft_lemma_size                       3
% 23.70/3.47  --prop_impl_unit_size                   0
% 23.70/3.47  --prop_impl_unit                        []
% 23.70/3.47  --share_sel_clauses                     true
% 23.70/3.47  --reset_solvers                         false
% 23.70/3.47  --bc_imp_inh                            [conj_cone]
% 23.70/3.47  --conj_cone_tolerance                   3.
% 23.70/3.47  --extra_neg_conj                        none
% 23.70/3.47  --large_theory_mode                     true
% 23.70/3.47  --prolific_symb_bound                   200
% 23.70/3.47  --lt_threshold                          2000
% 23.70/3.47  --clause_weak_htbl                      true
% 23.70/3.47  --gc_record_bc_elim                     false
% 23.70/3.47  
% 23.70/3.47  ------ Preprocessing Options
% 23.70/3.47  
% 23.70/3.47  --preprocessing_flag                    true
% 23.70/3.47  --time_out_prep_mult                    0.1
% 23.70/3.47  --splitting_mode                        input
% 23.70/3.47  --splitting_grd                         true
% 23.70/3.47  --splitting_cvd                         false
% 23.70/3.47  --splitting_cvd_svl                     false
% 23.70/3.47  --splitting_nvd                         32
% 23.70/3.47  --sub_typing                            true
% 23.70/3.47  --prep_gs_sim                           true
% 23.70/3.47  --prep_unflatten                        true
% 23.70/3.47  --prep_res_sim                          true
% 23.70/3.47  --prep_upred                            true
% 23.70/3.47  --prep_sem_filter                       exhaustive
% 23.70/3.47  --prep_sem_filter_out                   false
% 23.70/3.47  --pred_elim                             true
% 23.70/3.47  --res_sim_input                         true
% 23.70/3.47  --eq_ax_congr_red                       true
% 23.70/3.47  --pure_diseq_elim                       true
% 23.70/3.47  --brand_transform                       false
% 23.70/3.47  --non_eq_to_eq                          false
% 23.70/3.47  --prep_def_merge                        true
% 23.70/3.47  --prep_def_merge_prop_impl              false
% 23.70/3.47  --prep_def_merge_mbd                    true
% 23.70/3.47  --prep_def_merge_tr_red                 false
% 23.70/3.47  --prep_def_merge_tr_cl                  false
% 23.70/3.47  --smt_preprocessing                     true
% 23.70/3.47  --smt_ac_axioms                         fast
% 23.70/3.47  --preprocessed_out                      false
% 23.70/3.47  --preprocessed_stats                    false
% 23.70/3.47  
% 23.70/3.47  ------ Abstraction refinement Options
% 23.70/3.47  
% 23.70/3.47  --abstr_ref                             []
% 23.70/3.47  --abstr_ref_prep                        false
% 23.70/3.47  --abstr_ref_until_sat                   false
% 23.70/3.47  --abstr_ref_sig_restrict                funpre
% 23.70/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.70/3.47  --abstr_ref_under                       []
% 23.70/3.47  
% 23.70/3.47  ------ SAT Options
% 23.70/3.47  
% 23.70/3.47  --sat_mode                              false
% 23.70/3.47  --sat_fm_restart_options                ""
% 23.70/3.47  --sat_gr_def                            false
% 23.70/3.47  --sat_epr_types                         true
% 23.70/3.47  --sat_non_cyclic_types                  false
% 23.70/3.47  --sat_finite_models                     false
% 23.70/3.47  --sat_fm_lemmas                         false
% 23.70/3.47  --sat_fm_prep                           false
% 23.70/3.47  --sat_fm_uc_incr                        true
% 23.70/3.47  --sat_out_model                         small
% 23.70/3.47  --sat_out_clauses                       false
% 23.70/3.47  
% 23.70/3.47  ------ QBF Options
% 23.70/3.47  
% 23.70/3.47  --qbf_mode                              false
% 23.70/3.47  --qbf_elim_univ                         false
% 23.70/3.47  --qbf_dom_inst                          none
% 23.70/3.47  --qbf_dom_pre_inst                      false
% 23.70/3.47  --qbf_sk_in                             false
% 23.70/3.47  --qbf_pred_elim                         true
% 23.70/3.47  --qbf_split                             512
% 23.70/3.47  
% 23.70/3.47  ------ BMC1 Options
% 23.70/3.47  
% 23.70/3.47  --bmc1_incremental                      false
% 23.70/3.47  --bmc1_axioms                           reachable_all
% 23.70/3.47  --bmc1_min_bound                        0
% 23.70/3.47  --bmc1_max_bound                        -1
% 23.70/3.47  --bmc1_max_bound_default                -1
% 23.70/3.47  --bmc1_symbol_reachability              true
% 23.70/3.47  --bmc1_property_lemmas                  false
% 23.70/3.47  --bmc1_k_induction                      false
% 23.70/3.47  --bmc1_non_equiv_states                 false
% 23.70/3.47  --bmc1_deadlock                         false
% 23.70/3.47  --bmc1_ucm                              false
% 23.70/3.47  --bmc1_add_unsat_core                   none
% 23.70/3.47  --bmc1_unsat_core_children              false
% 23.70/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.70/3.47  --bmc1_out_stat                         full
% 23.70/3.47  --bmc1_ground_init                      false
% 23.70/3.47  --bmc1_pre_inst_next_state              false
% 23.70/3.47  --bmc1_pre_inst_state                   false
% 23.70/3.47  --bmc1_pre_inst_reach_state             false
% 23.70/3.47  --bmc1_out_unsat_core                   false
% 23.70/3.47  --bmc1_aig_witness_out                  false
% 23.70/3.47  --bmc1_verbose                          false
% 23.70/3.47  --bmc1_dump_clauses_tptp                false
% 23.70/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.70/3.47  --bmc1_dump_file                        -
% 23.70/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.70/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.70/3.47  --bmc1_ucm_extend_mode                  1
% 23.70/3.47  --bmc1_ucm_init_mode                    2
% 23.70/3.47  --bmc1_ucm_cone_mode                    none
% 23.70/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.70/3.47  --bmc1_ucm_relax_model                  4
% 23.70/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.70/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.70/3.47  --bmc1_ucm_layered_model                none
% 23.70/3.47  --bmc1_ucm_max_lemma_size               10
% 23.70/3.47  
% 23.70/3.47  ------ AIG Options
% 23.70/3.47  
% 23.70/3.47  --aig_mode                              false
% 23.70/3.47  
% 23.70/3.47  ------ Instantiation Options
% 23.70/3.47  
% 23.70/3.47  --instantiation_flag                    true
% 23.70/3.47  --inst_sos_flag                         true
% 23.70/3.47  --inst_sos_phase                        true
% 23.70/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.70/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.70/3.47  --inst_lit_sel_side                     none
% 23.70/3.47  --inst_solver_per_active                1400
% 23.70/3.47  --inst_solver_calls_frac                1.
% 23.70/3.47  --inst_passive_queue_type               priority_queues
% 23.70/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.70/3.47  --inst_passive_queues_freq              [25;2]
% 23.70/3.47  --inst_dismatching                      true
% 23.70/3.47  --inst_eager_unprocessed_to_passive     true
% 23.70/3.47  --inst_prop_sim_given                   true
% 23.70/3.47  --inst_prop_sim_new                     false
% 23.70/3.47  --inst_subs_new                         false
% 23.70/3.47  --inst_eq_res_simp                      false
% 23.70/3.47  --inst_subs_given                       false
% 23.70/3.47  --inst_orphan_elimination               true
% 23.70/3.47  --inst_learning_loop_flag               true
% 23.70/3.47  --inst_learning_start                   3000
% 23.70/3.47  --inst_learning_factor                  2
% 23.70/3.47  --inst_start_prop_sim_after_learn       3
% 23.70/3.47  --inst_sel_renew                        solver
% 23.70/3.47  --inst_lit_activity_flag                true
% 23.70/3.47  --inst_restr_to_given                   false
% 23.70/3.47  --inst_activity_threshold               500
% 23.70/3.47  --inst_out_proof                        true
% 23.70/3.47  
% 23.70/3.47  ------ Resolution Options
% 23.70/3.47  
% 23.70/3.47  --resolution_flag                       false
% 23.70/3.47  --res_lit_sel                           adaptive
% 23.70/3.47  --res_lit_sel_side                      none
% 23.70/3.47  --res_ordering                          kbo
% 23.70/3.47  --res_to_prop_solver                    active
% 23.70/3.47  --res_prop_simpl_new                    false
% 23.70/3.47  --res_prop_simpl_given                  true
% 23.70/3.47  --res_passive_queue_type                priority_queues
% 23.70/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.70/3.47  --res_passive_queues_freq               [15;5]
% 23.70/3.47  --res_forward_subs                      full
% 23.70/3.47  --res_backward_subs                     full
% 23.70/3.47  --res_forward_subs_resolution           true
% 23.70/3.47  --res_backward_subs_resolution          true
% 23.70/3.47  --res_orphan_elimination                true
% 23.70/3.47  --res_time_limit                        2.
% 23.70/3.47  --res_out_proof                         true
% 23.70/3.47  
% 23.70/3.47  ------ Superposition Options
% 23.70/3.47  
% 23.70/3.47  --superposition_flag                    true
% 23.70/3.47  --sup_passive_queue_type                priority_queues
% 23.70/3.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.70/3.47  --sup_passive_queues_freq               [8;1;4]
% 23.70/3.47  --demod_completeness_check              fast
% 23.70/3.47  --demod_use_ground                      true
% 23.70/3.47  --sup_to_prop_solver                    passive
% 23.70/3.47  --sup_prop_simpl_new                    true
% 23.70/3.47  --sup_prop_simpl_given                  true
% 23.70/3.47  --sup_fun_splitting                     true
% 23.70/3.47  --sup_smt_interval                      50000
% 23.70/3.47  
% 23.70/3.47  ------ Superposition Simplification Setup
% 23.70/3.47  
% 23.70/3.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.70/3.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.70/3.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.70/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.70/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.70/3.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.70/3.47  --sup_immed_triv                        [TrivRules]
% 23.70/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.47  --sup_immed_bw_main                     []
% 23.70/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.70/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.70/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.47  --sup_input_bw                          []
% 23.70/3.47  
% 23.70/3.47  ------ Combination Options
% 23.70/3.47  
% 23.70/3.47  --comb_res_mult                         3
% 23.70/3.47  --comb_sup_mult                         2
% 23.70/3.47  --comb_inst_mult                        10
% 23.70/3.47  
% 23.70/3.47  ------ Debug Options
% 23.70/3.47  
% 23.70/3.47  --dbg_backtrace                         false
% 23.70/3.47  --dbg_dump_prop_clauses                 false
% 23.70/3.47  --dbg_dump_prop_clauses_file            -
% 23.70/3.47  --dbg_out_stat                          false
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  ------ Proving...
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  % SZS status Theorem for theBenchmark.p
% 23.70/3.47  
% 23.70/3.47  % SZS output start CNFRefutation for theBenchmark.p
% 23.70/3.47  
% 23.70/3.47  fof(f20,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f72,plain,(
% 23.70/3.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f20])).
% 23.70/3.47  
% 23.70/3.47  fof(f13,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f65,plain,(
% 23.70/3.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f13])).
% 23.70/3.47  
% 23.70/3.47  fof(f21,axiom,(
% 23.70/3.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f73,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.70/3.47    inference(cnf_transformation,[],[f21])).
% 23.70/3.47  
% 23.70/3.47  fof(f80,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 23.70/3.47    inference(definition_unfolding,[],[f73,f79])).
% 23.70/3.47  
% 23.70/3.47  fof(f15,axiom,(
% 23.70/3.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f67,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f15])).
% 23.70/3.47  
% 23.70/3.47  fof(f16,axiom,(
% 23.70/3.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f68,plain,(
% 23.70/3.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f16])).
% 23.70/3.47  
% 23.70/3.47  fof(f17,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f69,plain,(
% 23.70/3.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f17])).
% 23.70/3.47  
% 23.70/3.47  fof(f18,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f70,plain,(
% 23.70/3.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f18])).
% 23.70/3.47  
% 23.70/3.47  fof(f19,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f71,plain,(
% 23.70/3.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f19])).
% 23.70/3.47  
% 23.70/3.47  fof(f76,plain,(
% 23.70/3.47    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f70,f71])).
% 23.70/3.47  
% 23.70/3.47  fof(f77,plain,(
% 23.70/3.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f69,f76])).
% 23.70/3.47  
% 23.70/3.47  fof(f78,plain,(
% 23.70/3.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f68,f77])).
% 23.70/3.47  
% 23.70/3.47  fof(f79,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f67,f78])).
% 23.70/3.47  
% 23.70/3.47  fof(f83,plain,(
% 23.70/3.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 23.70/3.47    inference(definition_unfolding,[],[f65,f80,f71,f79])).
% 23.70/3.47  
% 23.70/3.47  fof(f97,plain,(
% 23.70/3.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 23.70/3.47    inference(definition_unfolding,[],[f72,f83])).
% 23.70/3.47  
% 23.70/3.47  fof(f12,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f64,plain,(
% 23.70/3.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f12])).
% 23.70/3.47  
% 23.70/3.47  fof(f14,axiom,(
% 23.70/3.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f66,plain,(
% 23.70/3.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f14])).
% 23.70/3.47  
% 23.70/3.47  fof(f82,plain,(
% 23.70/3.47    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f66,f79])).
% 23.70/3.47  
% 23.70/3.47  fof(f84,plain,(
% 23.70/3.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 23.70/3.47    inference(definition_unfolding,[],[f64,f80,f71,f82])).
% 23.70/3.47  
% 23.70/3.47  fof(f11,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f63,plain,(
% 23.70/3.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f11])).
% 23.70/3.47  
% 23.70/3.47  fof(f96,plain,(
% 23.70/3.47    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X3,X1,X0)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f63,f77,f77])).
% 23.70/3.47  
% 23.70/3.47  fof(f22,conjecture,(
% 23.70/3.47    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f23,negated_conjecture,(
% 23.70/3.47    ~! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 23.70/3.47    inference(negated_conjecture,[],[f22])).
% 23.70/3.47  
% 23.70/3.47  fof(f30,plain,(
% 23.70/3.47    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))),
% 23.70/3.47    inference(ennf_transformation,[],[f23])).
% 23.70/3.47  
% 23.70/3.47  fof(f39,plain,(
% 23.70/3.47    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)) => (~r2_hidden(sK2,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 23.70/3.47    introduced(choice_axiom,[])).
% 23.70/3.47  
% 23.70/3.47  fof(f40,plain,(
% 23.70/3.47    ~r2_hidden(sK2,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 23.70/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f39])).
% 23.70/3.47  
% 23.70/3.47  fof(f74,plain,(
% 23.70/3.47    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 23.70/3.47    inference(cnf_transformation,[],[f40])).
% 23.70/3.47  
% 23.70/3.47  fof(f9,axiom,(
% 23.70/3.47    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f54,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f9])).
% 23.70/3.47  
% 23.70/3.47  fof(f81,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 23.70/3.47    inference(definition_unfolding,[],[f54,f80])).
% 23.70/3.47  
% 23.70/3.47  fof(f98,plain,(
% 23.70/3.47    k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_tarski(k5_enumset1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 23.70/3.47    inference(definition_unfolding,[],[f74,f81,f79,f79])).
% 23.70/3.47  
% 23.70/3.47  fof(f7,axiom,(
% 23.70/3.47    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f52,plain,(
% 23.70/3.47    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f7])).
% 23.70/3.47  
% 23.70/3.47  fof(f1,axiom,(
% 23.70/3.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f41,plain,(
% 23.70/3.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f1])).
% 23.70/3.47  
% 23.70/3.47  fof(f6,axiom,(
% 23.70/3.47    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f51,plain,(
% 23.70/3.47    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 23.70/3.47    inference(cnf_transformation,[],[f6])).
% 23.70/3.47  
% 23.70/3.47  fof(f87,plain,(
% 23.70/3.47    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X0,X1))) )),
% 23.70/3.47    inference(definition_unfolding,[],[f51,f81])).
% 23.70/3.47  
% 23.70/3.47  fof(f5,axiom,(
% 23.70/3.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f26,plain,(
% 23.70/3.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.70/3.47    inference(rectify,[],[f5])).
% 23.70/3.47  
% 23.70/3.47  fof(f28,plain,(
% 23.70/3.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.70/3.47    inference(ennf_transformation,[],[f26])).
% 23.70/3.47  
% 23.70/3.47  fof(f32,plain,(
% 23.70/3.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.70/3.47    introduced(choice_axiom,[])).
% 23.70/3.47  
% 23.70/3.47  fof(f33,plain,(
% 23.70/3.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.70/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).
% 23.70/3.47  
% 23.70/3.47  fof(f50,plain,(
% 23.70/3.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 23.70/3.47    inference(cnf_transformation,[],[f33])).
% 23.70/3.47  
% 23.70/3.47  fof(f10,axiom,(
% 23.70/3.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f29,plain,(
% 23.70/3.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 23.70/3.47    inference(ennf_transformation,[],[f10])).
% 23.70/3.47  
% 23.70/3.47  fof(f34,plain,(
% 23.70/3.47    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.70/3.47    inference(nnf_transformation,[],[f29])).
% 23.70/3.47  
% 23.70/3.47  fof(f35,plain,(
% 23.70/3.47    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.70/3.47    inference(flattening,[],[f34])).
% 23.70/3.47  
% 23.70/3.47  fof(f36,plain,(
% 23.70/3.47    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.70/3.47    inference(rectify,[],[f35])).
% 23.70/3.47  
% 23.70/3.47  fof(f37,plain,(
% 23.70/3.47    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 23.70/3.47    introduced(choice_axiom,[])).
% 23.70/3.47  
% 23.70/3.47  fof(f38,plain,(
% 23.70/3.47    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.70/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 23.70/3.47  
% 23.70/3.47  fof(f57,plain,(
% 23.70/3.47    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.70/3.47    inference(cnf_transformation,[],[f38])).
% 23.70/3.47  
% 23.70/3.47  fof(f93,plain,(
% 23.70/3.47    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 23.70/3.47    inference(definition_unfolding,[],[f57,f78])).
% 23.70/3.47  
% 23.70/3.47  fof(f101,plain,(
% 23.70/3.47    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 23.70/3.47    inference(equality_resolution,[],[f93])).
% 23.70/3.47  
% 23.70/3.47  fof(f102,plain,(
% 23.70/3.47    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 23.70/3.47    inference(equality_resolution,[],[f101])).
% 23.70/3.47  
% 23.70/3.47  fof(f4,axiom,(
% 23.70/3.47    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f27,plain,(
% 23.70/3.47    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 23.70/3.47    inference(ennf_transformation,[],[f4])).
% 23.70/3.47  
% 23.70/3.47  fof(f31,plain,(
% 23.70/3.47    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 23.70/3.47    inference(nnf_transformation,[],[f27])).
% 23.70/3.47  
% 23.70/3.47  fof(f44,plain,(
% 23.70/3.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 23.70/3.47    inference(cnf_transformation,[],[f31])).
% 23.70/3.47  
% 23.70/3.47  fof(f8,axiom,(
% 23.70/3.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f53,plain,(
% 23.70/3.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 23.70/3.47    inference(cnf_transformation,[],[f8])).
% 23.70/3.47  
% 23.70/3.47  fof(f3,axiom,(
% 23.70/3.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f25,plain,(
% 23.70/3.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 23.70/3.47    inference(rectify,[],[f3])).
% 23.70/3.47  
% 23.70/3.47  fof(f43,plain,(
% 23.70/3.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 23.70/3.47    inference(cnf_transformation,[],[f25])).
% 23.70/3.47  
% 23.70/3.47  fof(f86,plain,(
% 23.70/3.47    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 23.70/3.47    inference(definition_unfolding,[],[f43,f81])).
% 23.70/3.47  
% 23.70/3.47  fof(f2,axiom,(
% 23.70/3.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 23.70/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.70/3.47  
% 23.70/3.47  fof(f24,plain,(
% 23.70/3.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 23.70/3.47    inference(rectify,[],[f2])).
% 23.70/3.47  
% 23.70/3.47  fof(f42,plain,(
% 23.70/3.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 23.70/3.47    inference(cnf_transformation,[],[f24])).
% 23.70/3.47  
% 23.70/3.47  fof(f85,plain,(
% 23.70/3.47    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 23.70/3.47    inference(definition_unfolding,[],[f42,f80])).
% 23.70/3.47  
% 23.70/3.47  fof(f75,plain,(
% 23.70/3.47    ~r2_hidden(sK2,sK4)),
% 23.70/3.47    inference(cnf_transformation,[],[f40])).
% 23.70/3.47  
% 23.70/3.47  cnf(c_23,plain,
% 23.70/3.47      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 23.70/3.47      inference(cnf_transformation,[],[f97]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_0,plain,
% 23.70/3.47      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 23.70/3.47      inference(cnf_transformation,[],[f84]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_1273,plain,
% 23.70/3.47      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_23,c_0]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_22,plain,
% 23.70/3.47      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X0,X1) ),
% 23.70/3.47      inference(cnf_transformation,[],[f96]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_25,negated_conjecture,
% 23.70/3.47      ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_tarski(k5_enumset1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.70/3.47      inference(cnf_transformation,[],[f98]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_12,plain,
% 23.70/3.47      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.70/3.47      inference(cnf_transformation,[],[f52]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_1,plain,
% 23.70/3.47      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.70/3.47      inference(cnf_transformation,[],[f41]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_243,negated_conjecture,
% 23.70/3.47      ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.70/3.47      inference(theory_normalisation,[status(thm)],[c_25,c_12,c_1]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_1149,plain,
% 23.70/3.47      ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.70/3.47      inference(demodulation,[status(thm)],[c_22,c_243]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_62583,plain,
% 23.70/3.47      ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.70/3.47      inference(demodulation,[status(thm)],[c_1273,c_1149]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_63166,plain,
% 23.70/3.47      ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_1273,c_62583]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_11,plain,
% 23.70/3.47      ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X0,X1)) ),
% 23.70/3.47      inference(cnf_transformation,[],[f87]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_244,plain,
% 23.70/3.47      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,X1)) ),
% 23.70/3.47      inference(theory_normalisation,[status(thm)],[c_11,c_12,c_1]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_514,plain,
% 23.70/3.47      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,X1)) = iProver_top ),
% 23.70/3.47      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_64548,plain,
% 23.70/3.47      ( r1_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = iProver_top ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_63166,c_514]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_8,plain,
% 23.70/3.47      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 23.70/3.47      inference(cnf_transformation,[],[f50]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_517,plain,
% 23.70/3.47      ( r1_xboole_0(X0,X1) != iProver_top
% 23.70/3.47      | r2_hidden(X2,X1) != iProver_top
% 23.70/3.47      | r2_hidden(X2,X0) != iProver_top ),
% 23.70/3.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_71907,plain,
% 23.70/3.47      ( r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 23.70/3.47      | r2_hidden(X0,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != iProver_top ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_64548,c_517]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_71909,plain,
% 23.70/3.47      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 23.70/3.47      | r2_hidden(sK2,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != iProver_top ),
% 23.70/3.47      inference(instantiation,[status(thm)],[c_71907]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_19,plain,
% 23.70/3.47      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
% 23.70/3.47      inference(cnf_transformation,[],[f102]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_45207,plain,
% 23.70/3.47      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.70/3.47      inference(instantiation,[status(thm)],[c_19]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_45208,plain,
% 23.70/3.47      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 23.70/3.47      inference(predicate_to_equality,[status(thm)],[c_45207]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_7,plain,
% 23.70/3.47      ( r2_hidden(X0,X1)
% 23.70/3.47      | r2_hidden(X0,X2)
% 23.70/3.47      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 23.70/3.47      inference(cnf_transformation,[],[f44]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_245,plain,
% 23.70/3.47      ( r2_hidden(X0,X1)
% 23.70/3.47      | r2_hidden(X0,X2)
% 23.70/3.47      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 23.70/3.47      inference(theory_normalisation,[status(thm)],[c_7,c_12,c_1]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_518,plain,
% 23.70/3.47      ( r2_hidden(X0,X1) = iProver_top
% 23.70/3.47      | r2_hidden(X0,X2) = iProver_top
% 23.70/3.47      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 23.70/3.47      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_29529,plain,
% 23.70/3.47      ( r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 23.70/3.47      | r2_hidden(X0,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) = iProver_top
% 23.70/3.47      | r2_hidden(X0,sK4) = iProver_top ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_1149,c_518]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_13,plain,
% 23.70/3.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.70/3.47      inference(cnf_transformation,[],[f53]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_1038,plain,
% 23.70/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_1578,plain,
% 23.70/3.47      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),X0)) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_1149,c_12]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_2141,plain,
% 23.70/3.47      ( k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0))) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_12,c_1578]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_14126,plain,
% 23.70/3.47      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0))) = k5_xboole_0(sK4,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_1038,c_2141]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_3,plain,
% 23.70/3.47      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 23.70/3.47      inference(cnf_transformation,[],[f86]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_248,plain,
% 23.70/3.47      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 23.70/3.47      inference(theory_normalisation,[status(thm)],[c_3,c_12,c_1]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_2,plain,
% 23.70/3.47      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 23.70/3.47      inference(cnf_transformation,[],[f85]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_522,plain,
% 23.70/3.47      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.70/3.47      inference(light_normalisation,[status(thm)],[c_248,c_2,c_13]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_540,plain,
% 23.70/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_2706,plain,
% 23.70/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.70/3.47      inference(superposition,[status(thm)],[c_13,c_540]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_2756,plain,
% 23.70/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 23.70/3.47      inference(demodulation,[status(thm)],[c_2706,c_522]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_14189,plain,
% 23.70/3.47      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_tarski(k5_enumset1(sK4,sK4,sK4,sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) = k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.70/3.47      inference(demodulation,[status(thm)],[c_14126,c_522,c_2756]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_29598,plain,
% 23.70/3.47      ( r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 23.70/3.47      | r2_hidden(X0,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = iProver_top
% 23.70/3.47      | r2_hidden(X0,sK4) = iProver_top ),
% 23.70/3.47      inference(light_normalisation,[status(thm)],[c_29529,c_14189]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_29657,plain,
% 23.70/3.47      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 23.70/3.47      | r2_hidden(sK2,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = iProver_top
% 23.70/3.47      | r2_hidden(sK2,sK4) = iProver_top ),
% 23.70/3.47      inference(instantiation,[status(thm)],[c_29598]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_24,negated_conjecture,
% 23.70/3.47      ( ~ r2_hidden(sK2,sK4) ),
% 23.70/3.47      inference(cnf_transformation,[],[f75]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(c_26,plain,
% 23.70/3.47      ( r2_hidden(sK2,sK4) != iProver_top ),
% 23.70/3.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.70/3.47  
% 23.70/3.47  cnf(contradiction,plain,
% 23.70/3.47      ( $false ),
% 23.70/3.47      inference(minisat,[status(thm)],[c_71909,c_45208,c_29657,c_26]) ).
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  % SZS output end CNFRefutation for theBenchmark.p
% 23.70/3.47  
% 23.70/3.47  ------                               Statistics
% 23.70/3.47  
% 23.70/3.47  ------ General
% 23.70/3.47  
% 23.70/3.47  abstr_ref_over_cycles:                  0
% 23.70/3.47  abstr_ref_under_cycles:                 0
% 23.70/3.47  gc_basic_clause_elim:                   0
% 23.70/3.47  forced_gc_time:                         0
% 23.70/3.47  parsing_time:                           0.01
% 23.70/3.47  unif_index_cands_time:                  0.
% 23.70/3.47  unif_index_add_time:                    0.
% 23.70/3.47  orderings_time:                         0.
% 23.70/3.47  out_proof_time:                         0.01
% 23.70/3.47  total_time:                             2.888
% 23.70/3.47  num_of_symbols:                         42
% 23.70/3.47  num_of_terms:                           133902
% 23.70/3.47  
% 23.70/3.47  ------ Preprocessing
% 23.70/3.47  
% 23.70/3.47  num_of_splits:                          0
% 23.70/3.47  num_of_split_atoms:                     0
% 23.70/3.47  num_of_reused_defs:                     0
% 23.70/3.47  num_eq_ax_congr_red:                    12
% 23.70/3.47  num_of_sem_filtered_clauses:            1
% 23.70/3.47  num_of_subtypes:                        0
% 23.70/3.47  monotx_restored_types:                  0
% 23.70/3.47  sat_num_of_epr_types:                   0
% 23.70/3.47  sat_num_of_non_cyclic_types:            0
% 23.70/3.47  sat_guarded_non_collapsed_types:        0
% 23.70/3.47  num_pure_diseq_elim:                    0
% 23.70/3.47  simp_replaced_by:                       0
% 23.70/3.47  res_preprocessed:                       91
% 23.70/3.47  prep_upred:                             0
% 23.70/3.47  prep_unflattend:                        2
% 23.70/3.47  smt_new_axioms:                         0
% 23.70/3.47  pred_elim_cands:                        2
% 23.70/3.47  pred_elim:                              0
% 23.70/3.47  pred_elim_cl:                           0
% 23.70/3.47  pred_elim_cycles:                       1
% 23.70/3.47  merged_defs:                            0
% 23.70/3.47  merged_defs_ncl:                        0
% 23.70/3.47  bin_hyper_res:                          0
% 23.70/3.47  prep_cycles:                            3
% 23.70/3.47  pred_elim_time:                         0.
% 23.70/3.47  splitting_time:                         0.
% 23.70/3.47  sem_filter_time:                        0.
% 23.70/3.47  monotx_time:                            0.
% 23.70/3.47  subtype_inf_time:                       0.
% 23.70/3.47  
% 23.70/3.47  ------ Problem properties
% 23.70/3.47  
% 23.70/3.47  clauses:                                26
% 23.70/3.47  conjectures:                            2
% 23.70/3.47  epr:                                    2
% 23.70/3.47  horn:                                   19
% 23.70/3.47  ground:                                 2
% 23.70/3.47  unary:                                  14
% 23.70/3.47  binary:                                 2
% 23.70/3.47  lits:                                   51
% 23.70/3.47  lits_eq:                                22
% 23.70/3.47  fd_pure:                                0
% 23.70/3.47  fd_pseudo:                              0
% 23.70/3.47  fd_cond:                                0
% 23.70/3.47  fd_pseudo_cond:                         4
% 23.70/3.47  ac_symbols:                             1
% 23.70/3.47  
% 23.70/3.47  ------ Propositional Solver
% 23.70/3.47  
% 23.70/3.47  prop_solver_calls:                      27
% 23.70/3.47  prop_fast_solver_calls:                 712
% 23.70/3.47  smt_solver_calls:                       0
% 23.70/3.47  smt_fast_solver_calls:                  0
% 23.70/3.47  prop_num_of_clauses:                    15826
% 23.70/3.47  prop_preprocess_simplified:             20786
% 23.70/3.47  prop_fo_subsumed:                       1
% 23.70/3.47  prop_solver_time:                       0.
% 23.70/3.47  smt_solver_time:                        0.
% 23.70/3.47  smt_fast_solver_time:                   0.
% 23.70/3.47  prop_fast_solver_time:                  0.
% 23.70/3.47  prop_unsat_core_time:                   0.001
% 23.70/3.47  
% 23.70/3.47  ------ QBF
% 23.70/3.47  
% 23.70/3.47  qbf_q_res:                              0
% 23.70/3.47  qbf_num_tautologies:                    0
% 23.70/3.47  qbf_prep_cycles:                        0
% 23.70/3.47  
% 23.70/3.47  ------ BMC1
% 23.70/3.47  
% 23.70/3.47  bmc1_current_bound:                     -1
% 23.70/3.47  bmc1_last_solved_bound:                 -1
% 23.70/3.47  bmc1_unsat_core_size:                   -1
% 23.70/3.47  bmc1_unsat_core_parents_size:           -1
% 23.70/3.47  bmc1_merge_next_fun:                    0
% 23.70/3.47  bmc1_unsat_core_clauses_time:           0.
% 23.70/3.47  
% 23.70/3.47  ------ Instantiation
% 23.70/3.47  
% 23.70/3.47  inst_num_of_clauses:                    2392
% 23.70/3.47  inst_num_in_passive:                    959
% 23.70/3.47  inst_num_in_active:                     703
% 23.70/3.47  inst_num_in_unprocessed:                732
% 23.70/3.47  inst_num_of_loops:                      760
% 23.70/3.47  inst_num_of_learning_restarts:          0
% 23.70/3.47  inst_num_moves_active_passive:          55
% 23.70/3.47  inst_lit_activity:                      0
% 23.70/3.47  inst_lit_activity_moves:                0
% 23.70/3.47  inst_num_tautologies:                   0
% 23.70/3.47  inst_num_prop_implied:                  0
% 23.70/3.47  inst_num_existing_simplified:           0
% 23.70/3.47  inst_num_eq_res_simplified:             0
% 23.70/3.47  inst_num_child_elim:                    0
% 23.70/3.47  inst_num_of_dismatching_blockings:      10163
% 23.70/3.47  inst_num_of_non_proper_insts:           6013
% 23.70/3.47  inst_num_of_duplicates:                 0
% 23.70/3.47  inst_inst_num_from_inst_to_res:         0
% 23.70/3.47  inst_dismatching_checking_time:         0.
% 23.70/3.47  
% 23.70/3.47  ------ Resolution
% 23.70/3.47  
% 23.70/3.47  res_num_of_clauses:                     0
% 23.70/3.47  res_num_in_passive:                     0
% 23.70/3.47  res_num_in_active:                      0
% 23.70/3.47  res_num_of_loops:                       94
% 23.70/3.47  res_forward_subset_subsumed:            635
% 23.70/3.47  res_backward_subset_subsumed:           18
% 23.70/3.47  res_forward_subsumed:                   0
% 23.70/3.47  res_backward_subsumed:                  0
% 23.70/3.47  res_forward_subsumption_resolution:     0
% 23.70/3.47  res_backward_subsumption_resolution:    0
% 23.70/3.47  res_clause_to_clause_subsumption:       123921
% 23.70/3.47  res_orphan_elimination:                 0
% 23.70/3.47  res_tautology_del:                      380
% 23.70/3.47  res_num_eq_res_simplified:              0
% 23.70/3.47  res_num_sel_changes:                    0
% 23.70/3.47  res_moves_from_active_to_pass:          0
% 23.70/3.47  
% 23.70/3.47  ------ Superposition
% 23.70/3.47  
% 23.70/3.47  sup_time_total:                         0.
% 23.70/3.47  sup_time_generating:                    0.
% 23.70/3.47  sup_time_sim_full:                      0.
% 23.70/3.47  sup_time_sim_immed:                     0.
% 23.70/3.47  
% 23.70/3.47  sup_num_of_clauses:                     4490
% 23.70/3.47  sup_num_in_active:                      122
% 23.70/3.47  sup_num_in_passive:                     4368
% 23.70/3.47  sup_num_of_loops:                       150
% 23.70/3.47  sup_fw_superposition:                   11701
% 23.70/3.47  sup_bw_superposition:                   8278
% 23.70/3.47  sup_immediate_simplified:               13848
% 23.70/3.47  sup_given_eliminated:                   7
% 23.70/3.47  comparisons_done:                       0
% 23.70/3.47  comparisons_avoided:                    6
% 23.70/3.47  
% 23.70/3.47  ------ Simplifications
% 23.70/3.47  
% 23.70/3.47  
% 23.70/3.47  sim_fw_subset_subsumed:                 1
% 23.70/3.47  sim_bw_subset_subsumed:                 0
% 23.70/3.47  sim_fw_subsumed:                        832
% 23.70/3.47  sim_bw_subsumed:                        102
% 23.70/3.47  sim_fw_subsumption_res:                 0
% 23.70/3.47  sim_bw_subsumption_res:                 0
% 23.70/3.47  sim_tautology_del:                      15
% 23.70/3.47  sim_eq_tautology_del:                   5228
% 23.70/3.47  sim_eq_res_simp:                        0
% 23.70/3.47  sim_fw_demodulated:                     12092
% 23.70/3.47  sim_bw_demodulated:                     167
% 23.70/3.47  sim_light_normalised:                   6059
% 23.70/3.47  sim_joinable_taut:                      189
% 23.70/3.47  sim_joinable_simp:                      0
% 23.70/3.47  sim_ac_normalised:                      0
% 23.70/3.47  sim_smt_subsumption:                    0
% 23.70/3.47  
%------------------------------------------------------------------------------
