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
% DateTime   : Thu Dec  3 11:35:21 EST 2020

% Result     : Theorem 19.86s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :  155 (2172 expanded)
%              Number of clauses        :   63 ( 277 expanded)
%              Number of leaves         :   24 ( 631 expanded)
%              Depth                    :   25
%              Number of atoms          :  592 (7162 expanded)
%              Number of equality atoms :  246 (4052 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f56])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f97,f98])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f96,f107])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f95,f108])).

fof(f110,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f94,f109])).

fof(f111,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f93,f110])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f103,f111])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK6,sK8),sK7) != k1_tarski(sK6)
      & ( sK6 = sK8
        | ~ r2_hidden(sK8,sK7) )
      & r2_hidden(sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k3_xboole_0(k2_tarski(sK6,sK8),sK7) != k1_tarski(sK6)
    & ( sK6 = sK8
      | ~ r2_hidden(sK8,sK7) )
    & r2_hidden(sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f58])).

fof(f106,plain,(
    k3_xboole_0(k2_tarski(sK6,sK8),sK7) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f92,f111])).

fof(f136,plain,(
    k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f106,f83,f111,f112])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f129,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f85,f110])).

fof(f149,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f129])).

fof(f150,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f149])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f104,plain,(
    r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f130,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f84,f110])).

fof(f151,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f105,plain,
    ( sK6 = sK8
    | ~ r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f83])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f127,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f87,f110])).

fof(f145,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f127])).

fof(f146,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f145])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f128,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f86,f110])).

fof(f147,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f128])).

fof(f148,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f147])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5134,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X3,X1)
    | ~ r2_hidden(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) ),
    inference(resolution,[status(thm)],[c_33,c_3])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_36,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_6905,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8))
    | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

cnf(c_61257,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
    | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK8,X0)
    | ~ r2_hidden(sK6,X0) ),
    inference(resolution,[status(thm)],[c_5134,c_6905])).

cnf(c_29,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_56,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5148,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7) ),
    inference(resolution,[status(thm)],[c_5,c_36])).

cnf(c_38,negated_conjecture,
    ( r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1458,plain,
    ( ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(sK6,sK7)
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1460,plain,
    ( ~ r2_hidden(sK6,sK7)
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_1729,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
    | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
    | ~ r1_tarski(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3148,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
    | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
    | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_3150,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
    | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_5181,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5148,c_38,c_1460,c_3150])).

cnf(c_582,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_578,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3084,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_582,c_578])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_7716,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK8
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_6905,c_30])).

cnf(c_7726,plain,
    ( sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK8
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_7716,c_30])).

cnf(c_15155,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
    | ~ r2_hidden(sK8,X0)
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_3084,c_7726])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_16397,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
    | ~ r2_hidden(sK8,k4_xboole_0(X1,X0))
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_15155,c_14])).

cnf(c_19653,plain,
    ( ~ r2_hidden(sK8,k4_xboole_0(X0,sK7))
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_16397,c_5181])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_19688,plain,
    ( ~ r2_hidden(sK8,X0)
    | r2_hidden(sK8,sK7)
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_19653,c_13])).

cnf(c_37,negated_conjecture,
    ( ~ r2_hidden(sK8,sK7)
    | sK6 = sK8 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_579,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8018,plain,
    ( X0 != sK8
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = X0
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_7726,c_579])).

cnf(c_8401,plain,
    ( sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6
    | sK6 != sK8 ),
    inference(factoring,[status(thm)],[c_8018])).

cnf(c_53,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1267,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X0
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != X0
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_1556,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1557,plain,
    ( ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1294,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK7)
    | X1 != sK7
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1670,plain,
    ( r2_hidden(sK8,sK7)
    | ~ r2_hidden(sK6,sK7)
    | sK7 != sK7
    | sK8 != sK6 ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1764,plain,
    ( ~ r2_hidden(sK8,sK7)
    | ~ r2_hidden(sK6,sK7)
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2436,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_2448,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_583,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_1757,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
    | sK6 != X0
    | sK6 != X1
    | sK6 != X2
    | sK6 != X3
    | sK6 != X4
    | sK6 != X5
    | sK6 != X6
    | sK6 != X7 ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_2867,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)
    | sK6 != sK8
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_2246,plain,
    ( sK8 != X0
    | sK8 = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_4257,plain,
    ( sK8 != sK8
    | sK8 = sK6
    | sK6 != sK8 ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_12217,plain,
    ( sK6 != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8401,c_38,c_36,c_53,c_56,c_1556,c_1557,c_1670,c_1764,c_2436,c_2448,c_2867,c_4257])).

cnf(c_24190,plain,
    ( ~ r2_hidden(sK8,X0)
    | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19688,c_38,c_37,c_36,c_53,c_56,c_1556,c_1557,c_1670,c_1764,c_2436,c_2448,c_2867,c_4257])).

cnf(c_27,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_24222,plain,
    ( sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_24190,c_27])).

cnf(c_25415,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
    | ~ r2_hidden(sK6,X0) ),
    inference(resolution,[status(thm)],[c_24222,c_3084])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_26327,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8))
    | ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
    | ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(resolution,[status(thm)],[c_25415,c_4])).

cnf(c_65110,plain,
    ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61257,c_38,c_36,c_56,c_1460,c_3150,c_5148,c_6905,c_26327])).

cnf(c_65122,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8))
    | ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
    | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(resolution,[status(thm)],[c_65110,c_4])).

cnf(c_73014,plain,
    ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_65122,c_38,c_36,c_56,c_1460,c_3150,c_5148,c_26327])).

cnf(c_73027,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)) ),
    inference(resolution,[status(thm)],[c_73014,c_25415])).

cnf(c_28,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_16525,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73027,c_16525])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.86/3.11  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.86/3.11  
% 19.86/3.11  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.86/3.11  
% 19.86/3.11  ------  iProver source info
% 19.86/3.11  
% 19.86/3.11  git: date: 2020-06-30 10:37:57 +0100
% 19.86/3.11  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.86/3.11  git: non_committed_changes: false
% 19.86/3.11  git: last_make_outside_of_git: false
% 19.86/3.11  
% 19.86/3.11  ------ 
% 19.86/3.11  ------ Parsing...
% 19.86/3.11  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.86/3.11  
% 19.86/3.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.86/3.11  
% 19.86/3.11  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.86/3.11  
% 19.86/3.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.86/3.11  ------ Proving...
% 19.86/3.11  ------ Problem Properties 
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  clauses                                 38
% 19.86/3.11  conjectures                             3
% 19.86/3.11  EPR                                     5
% 19.86/3.11  Horn                                    26
% 19.86/3.11  unary                                   9
% 19.86/3.11  binary                                  11
% 19.86/3.11  lits                                    90
% 19.86/3.11  lits eq                                 32
% 19.86/3.11  fd_pure                                 0
% 19.86/3.11  fd_pseudo                               0
% 19.86/3.11  fd_cond                                 1
% 19.86/3.11  fd_pseudo_cond                          13
% 19.86/3.11  AC symbols                              0
% 19.86/3.11  
% 19.86/3.11  ------ Input Options Time Limit: Unbounded
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  ------ 
% 19.86/3.11  Current options:
% 19.86/3.11  ------ 
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  ------ Proving...
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  % SZS status Theorem for theBenchmark.p
% 19.86/3.11  
% 19.86/3.11  % SZS output start CNFRefutation for theBenchmark.p
% 19.86/3.11  
% 19.86/3.11  fof(f20,axiom,(
% 19.86/3.11    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f56,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.86/3.11    inference(nnf_transformation,[],[f20])).
% 19.86/3.11  
% 19.86/3.11  fof(f57,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.86/3.11    inference(flattening,[],[f56])).
% 19.86/3.11  
% 19.86/3.11  fof(f103,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f57])).
% 19.86/3.11  
% 19.86/3.11  fof(f13,axiom,(
% 19.86/3.11    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f93,plain,(
% 19.86/3.11    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f13])).
% 19.86/3.11  
% 19.86/3.11  fof(f14,axiom,(
% 19.86/3.11    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f94,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f14])).
% 19.86/3.11  
% 19.86/3.11  fof(f15,axiom,(
% 19.86/3.11    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f95,plain,(
% 19.86/3.11    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f15])).
% 19.86/3.11  
% 19.86/3.11  fof(f16,axiom,(
% 19.86/3.11    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f96,plain,(
% 19.86/3.11    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f16])).
% 19.86/3.11  
% 19.86/3.11  fof(f17,axiom,(
% 19.86/3.11    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f97,plain,(
% 19.86/3.11    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f17])).
% 19.86/3.11  
% 19.86/3.11  fof(f18,axiom,(
% 19.86/3.11    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f98,plain,(
% 19.86/3.11    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f18])).
% 19.86/3.11  
% 19.86/3.11  fof(f107,plain,(
% 19.86/3.11    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f97,f98])).
% 19.86/3.11  
% 19.86/3.11  fof(f108,plain,(
% 19.86/3.11    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f96,f107])).
% 19.86/3.11  
% 19.86/3.11  fof(f109,plain,(
% 19.86/3.11    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f95,f108])).
% 19.86/3.11  
% 19.86/3.11  fof(f110,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f94,f109])).
% 19.86/3.11  
% 19.86/3.11  fof(f111,plain,(
% 19.86/3.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f93,f110])).
% 19.86/3.11  
% 19.86/3.11  fof(f133,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f103,f111])).
% 19.86/3.11  
% 19.86/3.11  fof(f2,axiom,(
% 19.86/3.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f24,plain,(
% 19.86/3.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.86/3.11    inference(ennf_transformation,[],[f2])).
% 19.86/3.11  
% 19.86/3.11  fof(f31,plain,(
% 19.86/3.11    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.86/3.11    inference(nnf_transformation,[],[f24])).
% 19.86/3.11  
% 19.86/3.11  fof(f32,plain,(
% 19.86/3.11    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.86/3.11    inference(rectify,[],[f31])).
% 19.86/3.11  
% 19.86/3.11  fof(f33,plain,(
% 19.86/3.11    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.86/3.11    introduced(choice_axiom,[])).
% 19.86/3.11  
% 19.86/3.11  fof(f34,plain,(
% 19.86/3.11    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.86/3.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 19.86/3.11  
% 19.86/3.11  fof(f61,plain,(
% 19.86/3.11    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f34])).
% 19.86/3.11  
% 19.86/3.11  fof(f3,axiom,(
% 19.86/3.11    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f35,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(nnf_transformation,[],[f3])).
% 19.86/3.11  
% 19.86/3.11  fof(f36,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(flattening,[],[f35])).
% 19.86/3.11  
% 19.86/3.11  fof(f37,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(rectify,[],[f36])).
% 19.86/3.11  
% 19.86/3.11  fof(f38,plain,(
% 19.86/3.11    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.86/3.11    introduced(choice_axiom,[])).
% 19.86/3.11  
% 19.86/3.11  fof(f39,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 19.86/3.11  
% 19.86/3.11  fof(f67,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f39])).
% 19.86/3.11  
% 19.86/3.11  fof(f10,axiom,(
% 19.86/3.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f83,plain,(
% 19.86/3.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.86/3.11    inference(cnf_transformation,[],[f10])).
% 19.86/3.11  
% 19.86/3.11  fof(f116,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f67,f83])).
% 19.86/3.11  
% 19.86/3.11  fof(f21,conjecture,(
% 19.86/3.11    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f22,negated_conjecture,(
% 19.86/3.11    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 19.86/3.11    inference(negated_conjecture,[],[f21])).
% 19.86/3.11  
% 19.86/3.11  fof(f29,plain,(
% 19.86/3.11    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 19.86/3.11    inference(ennf_transformation,[],[f22])).
% 19.86/3.11  
% 19.86/3.11  fof(f30,plain,(
% 19.86/3.11    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 19.86/3.11    inference(flattening,[],[f29])).
% 19.86/3.11  
% 19.86/3.11  fof(f58,plain,(
% 19.86/3.11    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK6,sK8),sK7) != k1_tarski(sK6) & (sK6 = sK8 | ~r2_hidden(sK8,sK7)) & r2_hidden(sK6,sK7))),
% 19.86/3.11    introduced(choice_axiom,[])).
% 19.86/3.11  
% 19.86/3.11  fof(f59,plain,(
% 19.86/3.11    k3_xboole_0(k2_tarski(sK6,sK8),sK7) != k1_tarski(sK6) & (sK6 = sK8 | ~r2_hidden(sK8,sK7)) & r2_hidden(sK6,sK7)),
% 19.86/3.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f58])).
% 19.86/3.11  
% 19.86/3.11  fof(f106,plain,(
% 19.86/3.11    k3_xboole_0(k2_tarski(sK6,sK8),sK7) != k1_tarski(sK6)),
% 19.86/3.11    inference(cnf_transformation,[],[f59])).
% 19.86/3.11  
% 19.86/3.11  fof(f12,axiom,(
% 19.86/3.11    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f92,plain,(
% 19.86/3.11    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f12])).
% 19.86/3.11  
% 19.86/3.11  fof(f112,plain,(
% 19.86/3.11    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f92,f111])).
% 19.86/3.11  
% 19.86/3.11  fof(f136,plain,(
% 19.86/3.11    k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),
% 19.86/3.11    inference(definition_unfolding,[],[f106,f83,f111,f112])).
% 19.86/3.11  
% 19.86/3.11  fof(f11,axiom,(
% 19.86/3.11    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f27,plain,(
% 19.86/3.11    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 19.86/3.11    inference(ennf_transformation,[],[f11])).
% 19.86/3.11  
% 19.86/3.11  fof(f49,plain,(
% 19.86/3.11    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.86/3.11    inference(nnf_transformation,[],[f27])).
% 19.86/3.11  
% 19.86/3.11  fof(f50,plain,(
% 19.86/3.11    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.86/3.11    inference(flattening,[],[f49])).
% 19.86/3.11  
% 19.86/3.11  fof(f51,plain,(
% 19.86/3.11    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.86/3.11    inference(rectify,[],[f50])).
% 19.86/3.11  
% 19.86/3.11  fof(f52,plain,(
% 19.86/3.11    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 19.86/3.11    introduced(choice_axiom,[])).
% 19.86/3.11  
% 19.86/3.11  fof(f53,plain,(
% 19.86/3.11    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.86/3.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 19.86/3.11  
% 19.86/3.11  fof(f85,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.86/3.11    inference(cnf_transformation,[],[f53])).
% 19.86/3.11  
% 19.86/3.11  fof(f129,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 19.86/3.11    inference(definition_unfolding,[],[f85,f110])).
% 19.86/3.11  
% 19.86/3.11  fof(f149,plain,(
% 19.86/3.11    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 19.86/3.11    inference(equality_resolution,[],[f129])).
% 19.86/3.11  
% 19.86/3.11  fof(f150,plain,(
% 19.86/3.11    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 19.86/3.11    inference(equality_resolution,[],[f149])).
% 19.86/3.11  
% 19.86/3.11  fof(f68,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f39])).
% 19.86/3.11  
% 19.86/3.11  fof(f115,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f68,f83])).
% 19.86/3.11  
% 19.86/3.11  fof(f104,plain,(
% 19.86/3.11    r2_hidden(sK6,sK7)),
% 19.86/3.11    inference(cnf_transformation,[],[f59])).
% 19.86/3.11  
% 19.86/3.11  fof(f84,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 19.86/3.11    inference(cnf_transformation,[],[f53])).
% 19.86/3.11  
% 19.86/3.11  fof(f130,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 19.86/3.11    inference(definition_unfolding,[],[f84,f110])).
% 19.86/3.11  
% 19.86/3.11  fof(f151,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 19.86/3.11    inference(equality_resolution,[],[f130])).
% 19.86/3.11  
% 19.86/3.11  fof(f4,axiom,(
% 19.86/3.11    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f40,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(nnf_transformation,[],[f4])).
% 19.86/3.11  
% 19.86/3.11  fof(f41,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(flattening,[],[f40])).
% 19.86/3.11  
% 19.86/3.11  fof(f42,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(rectify,[],[f41])).
% 19.86/3.11  
% 19.86/3.11  fof(f43,plain,(
% 19.86/3.11    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 19.86/3.11    introduced(choice_axiom,[])).
% 19.86/3.11  
% 19.86/3.11  fof(f44,plain,(
% 19.86/3.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.86/3.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 19.86/3.11  
% 19.86/3.11  fof(f71,plain,(
% 19.86/3.11    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.86/3.11    inference(cnf_transformation,[],[f44])).
% 19.86/3.11  
% 19.86/3.11  fof(f141,plain,(
% 19.86/3.11    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 19.86/3.11    inference(equality_resolution,[],[f71])).
% 19.86/3.11  
% 19.86/3.11  fof(f72,plain,(
% 19.86/3.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 19.86/3.11    inference(cnf_transformation,[],[f44])).
% 19.86/3.11  
% 19.86/3.11  fof(f140,plain,(
% 19.86/3.11    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 19.86/3.11    inference(equality_resolution,[],[f72])).
% 19.86/3.11  
% 19.86/3.11  fof(f105,plain,(
% 19.86/3.11    sK6 = sK8 | ~r2_hidden(sK8,sK7)),
% 19.86/3.11    inference(cnf_transformation,[],[f59])).
% 19.86/3.11  
% 19.86/3.11  fof(f9,axiom,(
% 19.86/3.11    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.86/3.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.86/3.11  
% 19.86/3.11  fof(f26,plain,(
% 19.86/3.11    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.86/3.11    inference(ennf_transformation,[],[f9])).
% 19.86/3.11  
% 19.86/3.11  fof(f82,plain,(
% 19.86/3.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f26])).
% 19.86/3.11  
% 19.86/3.11  fof(f122,plain,(
% 19.86/3.11    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f82,f83])).
% 19.86/3.11  
% 19.86/3.11  fof(f87,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.86/3.11    inference(cnf_transformation,[],[f53])).
% 19.86/3.11  
% 19.86/3.11  fof(f127,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 19.86/3.11    inference(definition_unfolding,[],[f87,f110])).
% 19.86/3.11  
% 19.86/3.11  fof(f145,plain,(
% 19.86/3.11    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 19.86/3.11    inference(equality_resolution,[],[f127])).
% 19.86/3.11  
% 19.86/3.11  fof(f146,plain,(
% 19.86/3.11    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 19.86/3.11    inference(equality_resolution,[],[f145])).
% 19.86/3.11  
% 19.86/3.11  fof(f69,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.86/3.11    inference(cnf_transformation,[],[f39])).
% 19.86/3.11  
% 19.86/3.11  fof(f114,plain,(
% 19.86/3.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.86/3.11    inference(definition_unfolding,[],[f69,f83])).
% 19.86/3.11  
% 19.86/3.11  fof(f86,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.86/3.11    inference(cnf_transformation,[],[f53])).
% 19.86/3.11  
% 19.86/3.11  fof(f128,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 19.86/3.11    inference(definition_unfolding,[],[f86,f110])).
% 19.86/3.11  
% 19.86/3.11  fof(f147,plain,(
% 19.86/3.11    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 19.86/3.11    inference(equality_resolution,[],[f128])).
% 19.86/3.11  
% 19.86/3.11  fof(f148,plain,(
% 19.86/3.11    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 19.86/3.11    inference(equality_resolution,[],[f147])).
% 19.86/3.11  
% 19.86/3.11  cnf(c_33,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1)
% 19.86/3.11      | ~ r2_hidden(X2,X1)
% 19.86/3.11      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 19.86/3.11      inference(cnf_transformation,[],[f133]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_3,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.86/3.11      inference(cnf_transformation,[],[f61]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_5134,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1)
% 19.86/3.11      | ~ r2_hidden(X2,X1)
% 19.86/3.11      | r2_hidden(X3,X1)
% 19.86/3.11      | ~ r2_hidden(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_33,c_3]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_6,plain,
% 19.86/3.11      ( r2_hidden(sK1(X0,X1,X2),X0)
% 19.86/3.11      | r2_hidden(sK1(X0,X1,X2),X2)
% 19.86/3.11      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 19.86/3.11      inference(cnf_transformation,[],[f116]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_36,negated_conjecture,
% 19.86/3.11      ( k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 19.86/3.11      inference(cnf_transformation,[],[f136]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_6905,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8))
% 19.86/3.11      | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_6,c_36]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_61257,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
% 19.86/3.11      | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 19.86/3.11      | ~ r2_hidden(sK8,X0)
% 19.86/3.11      | ~ r2_hidden(sK6,X0) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_5134,c_6905]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_29,plain,
% 19.86/3.11      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 19.86/3.11      inference(cnf_transformation,[],[f150]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_56,plain,
% 19.86/3.11      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_29]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_5,plain,
% 19.86/3.11      ( r2_hidden(sK1(X0,X1,X2),X1)
% 19.86/3.11      | r2_hidden(sK1(X0,X1,X2),X2)
% 19.86/3.11      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 19.86/3.11      inference(cnf_transformation,[],[f115]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_5148,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 19.86/3.11      | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_5,c_36]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_38,negated_conjecture,
% 19.86/3.11      ( r2_hidden(sK6,sK7) ),
% 19.86/3.11      inference(cnf_transformation,[],[f104]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1458,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,sK7)
% 19.86/3.11      | ~ r2_hidden(sK6,sK7)
% 19.86/3.11      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0),sK7) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_33]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1460,plain,
% 19.86/3.11      ( ~ r2_hidden(sK6,sK7)
% 19.86/3.11      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK7) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_1458]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1729,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
% 19.86/3.11      | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
% 19.86/3.11      | ~ r1_tarski(X0,sK7) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_3]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_3148,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
% 19.86/3.11      | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
% 19.86/3.11      | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0),sK7) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_1729]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_3150,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 19.86/3.11      | r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
% 19.86/3.11      | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK7) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_3148]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_5181,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7) ),
% 19.86/3.11      inference(global_propositional_subsumption,
% 19.86/3.11                [status(thm)],
% 19.86/3.11                [c_5148,c_38,c_1460,c_3150]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_582,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.86/3.11      theory(equality) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_578,plain,( X0 = X0 ),theory(equality) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_3084,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_582,c_578]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_30,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 19.86/3.11      | X0 = X1
% 19.86/3.11      | X0 = X2
% 19.86/3.11      | X0 = X3 ),
% 19.86/3.11      inference(cnf_transformation,[],[f151]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_7716,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK8
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_6905,c_30]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_7726,plain,
% 19.86/3.11      ( sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK8
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_7716,c_30]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_15155,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
% 19.86/3.11      | ~ r2_hidden(sK8,X0)
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_3084,c_7726]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_14,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 19.86/3.11      inference(cnf_transformation,[],[f141]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_16397,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
% 19.86/3.11      | ~ r2_hidden(sK8,k4_xboole_0(X1,X0))
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_15155,c_14]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_19653,plain,
% 19.86/3.11      ( ~ r2_hidden(sK8,k4_xboole_0(X0,sK7))
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_16397,c_5181]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_13,plain,
% 19.86/3.11      ( ~ r2_hidden(X0,X1)
% 19.86/3.11      | r2_hidden(X0,X2)
% 19.86/3.11      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 19.86/3.11      inference(cnf_transformation,[],[f140]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_19688,plain,
% 19.86/3.11      ( ~ r2_hidden(sK8,X0)
% 19.86/3.11      | r2_hidden(sK8,sK7)
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_19653,c_13]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_37,negated_conjecture,
% 19.86/3.11      ( ~ r2_hidden(sK8,sK7) | sK6 = sK8 ),
% 19.86/3.11      inference(cnf_transformation,[],[f105]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_579,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_8018,plain,
% 19.86/3.11      ( X0 != sK8
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = X0
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_7726,c_579]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_8401,plain,
% 19.86/3.11      ( sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6
% 19.86/3.11      | sK6 != sK8 ),
% 19.86/3.11      inference(factoring,[status(thm)],[c_8018]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_53,plain,
% 19.86/3.11      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 19.86/3.11      | sK6 = sK6 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_30]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1267,plain,
% 19.86/3.11      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X0
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != X0
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_579]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1556,plain,
% 19.86/3.11      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_1267]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_22,plain,
% 19.86/3.11      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.86/3.11      inference(cnf_transformation,[],[f122]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1557,plain,
% 19.86/3.11      ( ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_22]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1294,plain,
% 19.86/3.11      ( r2_hidden(X0,X1) | ~ r2_hidden(sK6,sK7) | X1 != sK7 | X0 != sK6 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_582]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1670,plain,
% 19.86/3.11      ( r2_hidden(sK8,sK7)
% 19.86/3.11      | ~ r2_hidden(sK6,sK7)
% 19.86/3.11      | sK7 != sK7
% 19.86/3.11      | sK8 != sK6 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_1294]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1764,plain,
% 19.86/3.11      ( ~ r2_hidden(sK8,sK7)
% 19.86/3.11      | ~ r2_hidden(sK6,sK7)
% 19.86/3.11      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_1458]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_2436,plain,
% 19.86/3.11      ( sK8 = sK8 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_578]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_2448,plain,
% 19.86/3.11      ( sK7 = sK7 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_578]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_583,plain,
% 19.86/3.11      ( X0 != X1
% 19.86/3.11      | X2 != X3
% 19.86/3.11      | X4 != X5
% 19.86/3.11      | X6 != X7
% 19.86/3.11      | X8 != X9
% 19.86/3.11      | X10 != X11
% 19.86/3.11      | X12 != X13
% 19.86/3.11      | X14 != X15
% 19.86/3.11      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 19.86/3.11      theory(equality) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_1757,plain,
% 19.86/3.11      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
% 19.86/3.11      | sK6 != X0
% 19.86/3.11      | sK6 != X1
% 19.86/3.11      | sK6 != X2
% 19.86/3.11      | sK6 != X3
% 19.86/3.11      | sK6 != X4
% 19.86/3.11      | sK6 != X5
% 19.86/3.11      | sK6 != X6
% 19.86/3.11      | sK6 != X7 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_583]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_2867,plain,
% 19.86/3.11      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)
% 19.86/3.11      | sK6 != sK8
% 19.86/3.11      | sK6 != sK6 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_1757]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_2246,plain,
% 19.86/3.11      ( sK8 != X0 | sK8 = sK6 | sK6 != X0 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_579]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_4257,plain,
% 19.86/3.11      ( sK8 != sK8 | sK8 = sK6 | sK6 != sK8 ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_2246]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_12217,plain,
% 19.86/3.11      ( sK6 != sK8 ),
% 19.86/3.11      inference(global_propositional_subsumption,
% 19.86/3.11                [status(thm)],
% 19.86/3.11                [c_8401,c_38,c_36,c_53,c_56,c_1556,c_1557,c_1670,c_1764,
% 19.86/3.11                 c_2436,c_2448,c_2867,c_4257]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_24190,plain,
% 19.86/3.11      ( ~ r2_hidden(sK8,X0)
% 19.86/3.11      | sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(global_propositional_subsumption,
% 19.86/3.11                [status(thm)],
% 19.86/3.11                [c_19688,c_38,c_37,c_36,c_53,c_56,c_1556,c_1557,c_1670,
% 19.86/3.11                 c_1764,c_2436,c_2448,c_2867,c_4257]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_27,plain,
% 19.86/3.11      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 19.86/3.11      inference(cnf_transformation,[],[f146]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_24222,plain,
% 19.86/3.11      ( sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_24190,c_27]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_25415,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),X0)
% 19.86/3.11      | ~ r2_hidden(sK6,X0) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_24222,c_3084]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_4,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 19.86/3.11      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 19.86/3.11      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 19.86/3.11      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 19.86/3.11      inference(cnf_transformation,[],[f114]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_26327,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8))
% 19.86/3.11      | ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
% 19.86/3.11      | ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_25415,c_4]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_65110,plain,
% 19.86/3.11      ( r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 19.86/3.11      inference(global_propositional_subsumption,
% 19.86/3.11                [status(thm)],
% 19.86/3.11                [c_61257,c_38,c_36,c_56,c_1460,c_3150,c_5148,c_6905,
% 19.86/3.11                 c_26327]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_65122,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8))
% 19.86/3.11      | ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK7)
% 19.86/3.11      | k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),k4_xboole_0(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7)) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_65110,c_4]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_73014,plain,
% 19.86/3.11      ( ~ r2_hidden(sK1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8),sK7,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)) ),
% 19.86/3.11      inference(global_propositional_subsumption,
% 19.86/3.11                [status(thm)],
% 19.86/3.11                [c_65122,c_38,c_36,c_56,c_1460,c_3150,c_5148,c_26327]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_73027,plain,
% 19.86/3.11      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)) ),
% 19.86/3.11      inference(resolution,[status(thm)],[c_73014,c_25415]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_28,plain,
% 19.86/3.11      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 19.86/3.11      inference(cnf_transformation,[],[f148]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(c_16525,plain,
% 19.86/3.11      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK8)) ),
% 19.86/3.11      inference(instantiation,[status(thm)],[c_28]) ).
% 19.86/3.11  
% 19.86/3.11  cnf(contradiction,plain,
% 19.86/3.11      ( $false ),
% 19.86/3.11      inference(minisat,[status(thm)],[c_73027,c_16525]) ).
% 19.86/3.11  
% 19.86/3.11  
% 19.86/3.11  % SZS output end CNFRefutation for theBenchmark.p
% 19.86/3.11  
% 19.86/3.11  ------                               Statistics
% 19.86/3.11  
% 19.86/3.11  ------ Selected
% 19.86/3.11  
% 19.86/3.11  total_time:                             2.441
% 19.86/3.11  
%------------------------------------------------------------------------------
