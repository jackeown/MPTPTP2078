%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:32 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 630 expanded)
%              Number of clauses        :   30 (  70 expanded)
%              Number of leaves         :   16 ( 183 expanded)
%              Depth                    :   19
%              Number of atoms          :  333 (1750 expanded)
%              Number of equality atoms :  200 (1175 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f29])).

fof(f56,plain,(
    k3_xboole_0(sK3,sK4) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f82,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f56,f39,f64])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f24])).

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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f92,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f55,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f37,f39,f39,f39,f39])).

fof(f58,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f58,f39,f64])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f90,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f91,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

fof(f57,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_430,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_417,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_958,plain,
    ( sK5 = X0
    | r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_417])).

cnf(c_7460,plain,
    ( sK0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),X1) = sK5
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = X1
    | r2_hidden(sK0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_958])).

cnf(c_8976,plain,
    ( sK0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_7460,c_958])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_415,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_425,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1124,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_415,c_425])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1388,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1124,c_6])).

cnf(c_9212,plain,
    ( sK0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_8976,c_1388])).

cnf(c_16,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_448,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_16,c_18])).

cnf(c_10097,plain,
    ( sK0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9212,c_448])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_431,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15440,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10097,c_431])).

cnf(c_15444,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))
    | r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15440,c_10097])).

cnf(c_15445,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15444,c_1388])).

cnf(c_14,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_418,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_675,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_418])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15445,c_675,c_448,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:33:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.38/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/1.48  
% 7.38/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.38/1.48  
% 7.38/1.48  ------  iProver source info
% 7.38/1.48  
% 7.38/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.38/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.38/1.48  git: non_committed_changes: false
% 7.38/1.48  git: last_make_outside_of_git: false
% 7.38/1.48  
% 7.38/1.48  ------ 
% 7.38/1.48  ------ Parsing...
% 7.38/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.38/1.48  
% 7.38/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.38/1.48  
% 7.38/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.38/1.48  
% 7.38/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.38/1.48  ------ Proving...
% 7.38/1.48  ------ Problem Properties 
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  clauses                                 20
% 7.38/1.48  conjectures                             4
% 7.38/1.48  EPR                                     2
% 7.38/1.48  Horn                                    16
% 7.38/1.48  unary                                   8
% 7.38/1.48  binary                                  3
% 7.38/1.48  lits                                    45
% 7.38/1.48  lits eq                                 20
% 7.38/1.48  fd_pure                                 0
% 7.38/1.48  fd_pseudo                               0
% 7.38/1.48  fd_cond                                 0
% 7.38/1.48  fd_pseudo_cond                          7
% 7.38/1.48  AC symbols                              0
% 7.38/1.48  
% 7.38/1.48  ------ Input Options Time Limit: Unbounded
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  ------ 
% 7.38/1.48  Current options:
% 7.38/1.48  ------ 
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  ------ Proving...
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  % SZS status Theorem for theBenchmark.p
% 7.38/1.48  
% 7.38/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.38/1.48  
% 7.38/1.48  fof(f1,axiom,(
% 7.38/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f19,plain,(
% 7.38/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.38/1.48    inference(nnf_transformation,[],[f1])).
% 7.38/1.48  
% 7.38/1.48  fof(f20,plain,(
% 7.38/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.38/1.48    inference(flattening,[],[f19])).
% 7.38/1.48  
% 7.38/1.48  fof(f21,plain,(
% 7.38/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.38/1.48    inference(rectify,[],[f20])).
% 7.38/1.48  
% 7.38/1.48  fof(f22,plain,(
% 7.38/1.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.38/1.48    introduced(choice_axiom,[])).
% 7.38/1.48  
% 7.38/1.48  fof(f23,plain,(
% 7.38/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.38/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 7.38/1.48  
% 7.38/1.48  fof(f35,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f23])).
% 7.38/1.48  
% 7.38/1.48  fof(f4,axiom,(
% 7.38/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f39,plain,(
% 7.38/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.38/1.48    inference(cnf_transformation,[],[f4])).
% 7.38/1.48  
% 7.38/1.48  fof(f66,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f35,f39])).
% 7.38/1.48  
% 7.38/1.48  fof(f13,conjecture,(
% 7.38/1.48    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f14,negated_conjecture,(
% 7.38/1.48    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 7.38/1.48    inference(negated_conjecture,[],[f13])).
% 7.38/1.48  
% 7.38/1.48  fof(f17,plain,(
% 7.38/1.48    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 7.38/1.48    inference(ennf_transformation,[],[f14])).
% 7.38/1.48  
% 7.38/1.48  fof(f18,plain,(
% 7.38/1.48    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 7.38/1.48    inference(flattening,[],[f17])).
% 7.38/1.48  
% 7.38/1.48  fof(f29,plain,(
% 7.38/1.48    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3))),
% 7.38/1.48    introduced(choice_axiom,[])).
% 7.38/1.48  
% 7.38/1.48  fof(f30,plain,(
% 7.38/1.48    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3)),
% 7.38/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f29])).
% 7.38/1.48  
% 7.38/1.48  fof(f56,plain,(
% 7.38/1.48    k3_xboole_0(sK3,sK4) = k1_tarski(sK5)),
% 7.38/1.48    inference(cnf_transformation,[],[f30])).
% 7.38/1.48  
% 7.38/1.48  fof(f6,axiom,(
% 7.38/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f48,plain,(
% 7.38/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f6])).
% 7.38/1.48  
% 7.38/1.48  fof(f7,axiom,(
% 7.38/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f49,plain,(
% 7.38/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f7])).
% 7.38/1.48  
% 7.38/1.48  fof(f8,axiom,(
% 7.38/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f50,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f8])).
% 7.38/1.48  
% 7.38/1.48  fof(f9,axiom,(
% 7.38/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f51,plain,(
% 7.38/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f9])).
% 7.38/1.48  
% 7.38/1.48  fof(f10,axiom,(
% 7.38/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f52,plain,(
% 7.38/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f10])).
% 7.38/1.48  
% 7.38/1.48  fof(f11,axiom,(
% 7.38/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f53,plain,(
% 7.38/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f11])).
% 7.38/1.48  
% 7.38/1.48  fof(f12,axiom,(
% 7.38/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f54,plain,(
% 7.38/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f12])).
% 7.38/1.48  
% 7.38/1.48  fof(f59,plain,(
% 7.38/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f53,f54])).
% 7.38/1.48  
% 7.38/1.48  fof(f60,plain,(
% 7.38/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f52,f59])).
% 7.38/1.48  
% 7.38/1.48  fof(f61,plain,(
% 7.38/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f51,f60])).
% 7.38/1.48  
% 7.38/1.48  fof(f62,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f50,f61])).
% 7.38/1.48  
% 7.38/1.48  fof(f63,plain,(
% 7.38/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f49,f62])).
% 7.38/1.48  
% 7.38/1.48  fof(f64,plain,(
% 7.38/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f48,f63])).
% 7.38/1.48  
% 7.38/1.48  fof(f82,plain,(
% 7.38/1.48    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 7.38/1.48    inference(definition_unfolding,[],[f56,f39,f64])).
% 7.38/1.48  
% 7.38/1.48  fof(f5,axiom,(
% 7.38/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f16,plain,(
% 7.38/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.38/1.48    inference(ennf_transformation,[],[f5])).
% 7.38/1.48  
% 7.38/1.48  fof(f24,plain,(
% 7.38/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.38/1.48    inference(nnf_transformation,[],[f16])).
% 7.38/1.48  
% 7.38/1.48  fof(f25,plain,(
% 7.38/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.38/1.48    inference(flattening,[],[f24])).
% 7.38/1.48  
% 7.38/1.48  fof(f26,plain,(
% 7.38/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.38/1.48    inference(rectify,[],[f25])).
% 7.38/1.48  
% 7.38/1.48  fof(f27,plain,(
% 7.38/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.38/1.48    introduced(choice_axiom,[])).
% 7.38/1.48  
% 7.38/1.48  fof(f28,plain,(
% 7.38/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.38/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 7.38/1.48  
% 7.38/1.48  fof(f40,plain,(
% 7.38/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.38/1.48    inference(cnf_transformation,[],[f28])).
% 7.38/1.48  
% 7.38/1.48  fof(f80,plain,(
% 7.38/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.38/1.48    inference(definition_unfolding,[],[f40,f62])).
% 7.38/1.48  
% 7.38/1.48  fof(f92,plain,(
% 7.38/1.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 7.38/1.48    inference(equality_resolution,[],[f80])).
% 7.38/1.48  
% 7.38/1.48  fof(f55,plain,(
% 7.38/1.48    r1_tarski(sK2,sK3)),
% 7.38/1.48    inference(cnf_transformation,[],[f30])).
% 7.38/1.48  
% 7.38/1.48  fof(f3,axiom,(
% 7.38/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f15,plain,(
% 7.38/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.38/1.48    inference(ennf_transformation,[],[f3])).
% 7.38/1.48  
% 7.38/1.48  fof(f38,plain,(
% 7.38/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f15])).
% 7.38/1.48  
% 7.38/1.48  fof(f72,plain,(
% 7.38/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f38,f39])).
% 7.38/1.48  
% 7.38/1.48  fof(f2,axiom,(
% 7.38/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.38/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.48  
% 7.38/1.48  fof(f37,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f2])).
% 7.38/1.48  
% 7.38/1.48  fof(f71,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 7.38/1.48    inference(definition_unfolding,[],[f37,f39,f39,f39,f39])).
% 7.38/1.48  
% 7.38/1.48  fof(f58,plain,(
% 7.38/1.48    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 7.38/1.48    inference(cnf_transformation,[],[f30])).
% 7.38/1.48  
% 7.38/1.48  fof(f81,plain,(
% 7.38/1.48    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 7.38/1.48    inference(definition_unfolding,[],[f58,f39,f64])).
% 7.38/1.48  
% 7.38/1.48  fof(f36,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.38/1.48    inference(cnf_transformation,[],[f23])).
% 7.38/1.48  
% 7.38/1.48  fof(f65,plain,(
% 7.38/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.38/1.48    inference(definition_unfolding,[],[f36,f39])).
% 7.38/1.48  
% 7.38/1.48  fof(f41,plain,(
% 7.38/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.38/1.48    inference(cnf_transformation,[],[f28])).
% 7.38/1.48  
% 7.38/1.48  fof(f79,plain,(
% 7.38/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.38/1.48    inference(definition_unfolding,[],[f41,f62])).
% 7.38/1.48  
% 7.38/1.48  fof(f90,plain,(
% 7.38/1.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.38/1.48    inference(equality_resolution,[],[f79])).
% 7.38/1.48  
% 7.38/1.48  fof(f91,plain,(
% 7.38/1.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 7.38/1.48    inference(equality_resolution,[],[f90])).
% 7.38/1.48  
% 7.38/1.48  fof(f57,plain,(
% 7.38/1.48    r2_hidden(sK5,sK2)),
% 7.38/1.48    inference(cnf_transformation,[],[f30])).
% 7.38/1.48  
% 7.38/1.48  cnf(c_1,plain,
% 7.38/1.48      ( r2_hidden(sK0(X0,X1,X2),X1)
% 7.38/1.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.38/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 7.38/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_430,plain,
% 7.38/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 7.38/1.48      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 7.38/1.48      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_18,negated_conjecture,
% 7.38/1.48      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 7.38/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_15,plain,
% 7.38/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 7.38/1.48      | X0 = X1
% 7.38/1.48      | X0 = X2
% 7.38/1.48      | X0 = X3 ),
% 7.38/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_417,plain,
% 7.38/1.48      ( X0 = X1
% 7.38/1.48      | X0 = X2
% 7.38/1.48      | X0 = X3
% 7.38/1.48      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_958,plain,
% 7.38/1.48      ( sK5 = X0
% 7.38/1.48      | r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_18,c_417]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_7460,plain,
% 7.38/1.48      ( sK0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),X1) = sK5
% 7.38/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = X1
% 7.38/1.48      | r2_hidden(sK0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),X1),X1) = iProver_top ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_430,c_958]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_8976,plain,
% 7.38/1.48      ( sK0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5
% 7.38/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_7460,c_958]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_19,negated_conjecture,
% 7.38/1.48      ( r1_tarski(sK2,sK3) ),
% 7.38/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_415,plain,
% 7.38/1.48      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_7,plain,
% 7.38/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.38/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_425,plain,
% 7.38/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.38/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_1124,plain,
% 7.38/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_415,c_425]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_6,plain,
% 7.38/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 7.38/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_1388,plain,
% 7.38/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_1124,c_6]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_9212,plain,
% 7.38/1.48      ( sK0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5
% 7.38/1.48      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_8976,c_1388]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_16,negated_conjecture,
% 7.38/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 7.38/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_448,plain,
% 7.38/1.48      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 7.38/1.48      inference(light_normalisation,[status(thm)],[c_16,c_18]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_10097,plain,
% 7.38/1.48      ( sK0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = sK5 ),
% 7.38/1.48      inference(global_propositional_subsumption,
% 7.38/1.48                [status(thm)],
% 7.38/1.48                [c_9212,c_448]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_0,plain,
% 7.38/1.48      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.38/1.48      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.38/1.48      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.38/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 7.38/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_431,plain,
% 7.38/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 7.38/1.48      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.38/1.48      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.38/1.48      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_15440,plain,
% 7.38/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))
% 7.38/1.48      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
% 7.38/1.48      | r2_hidden(sK5,sK2) != iProver_top ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_10097,c_431]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_15444,plain,
% 7.38/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))
% 7.38/1.48      | r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
% 7.38/1.48      | r2_hidden(sK5,sK2) != iProver_top ),
% 7.38/1.48      inference(light_normalisation,[status(thm)],[c_15440,c_10097]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_15445,plain,
% 7.38/1.48      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
% 7.38/1.48      | r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top
% 7.38/1.48      | r2_hidden(sK5,sK2) != iProver_top ),
% 7.38/1.48      inference(demodulation,[status(thm)],[c_15444,c_1388]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_14,plain,
% 7.38/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 7.38/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_418,plain,
% 7.38/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_675,plain,
% 7.38/1.48      ( r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 7.38/1.48      inference(superposition,[status(thm)],[c_18,c_418]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_17,negated_conjecture,
% 7.38/1.48      ( r2_hidden(sK5,sK2) ),
% 7.38/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(c_21,plain,
% 7.38/1.48      ( r2_hidden(sK5,sK2) = iProver_top ),
% 7.38/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.38/1.48  
% 7.38/1.48  cnf(contradiction,plain,
% 7.38/1.48      ( $false ),
% 7.38/1.48      inference(minisat,[status(thm)],[c_15445,c_675,c_448,c_21]) ).
% 7.38/1.48  
% 7.38/1.48  
% 7.38/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.38/1.48  
% 7.38/1.48  ------                               Statistics
% 7.38/1.48  
% 7.38/1.48  ------ Selected
% 7.38/1.48  
% 7.38/1.48  total_time:                             0.539
% 7.38/1.48  
%------------------------------------------------------------------------------
