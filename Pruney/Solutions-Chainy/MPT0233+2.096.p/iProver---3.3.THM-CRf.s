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
% DateTime   : Thu Dec  3 11:31:26 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 221 expanded)
%              Number of clauses        :   32 (  34 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  297 ( 540 expanded)
%              Number of equality atoms :  197 ( 402 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f60,f70,f71])).

fof(f96,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK2 != sK5
      & sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( sK2 != sK5
    & sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f35])).

fof(f63,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f63,f70,f70])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f69])).

fof(f93,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f91,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f92,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f65,plain,(
    sK2 != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1018,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1015,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1030,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1221,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1015,c_1030])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1031,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1776,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1031])).

cnf(c_1875,plain,
    ( r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top
    | r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1776])).

cnf(c_2739,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1875])).

cnf(c_3433,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2739,c_1030])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1033,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8166,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3433,c_1033])).

cnf(c_8202,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8166])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2809,plain,
    ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
    | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2810,plain,
    ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top
    | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2809])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1190,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0,X1))
    | sK2 = X0
    | sK2 = X1
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1313,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))
    | sK2 = X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1802,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
    | sK2 = sK4
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1803,plain,
    ( sK2 = sK4
    | sK2 = sK5
    | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_40,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_42,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_19,negated_conjecture,
    ( sK2 != sK5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8202,c_2810,c_1803,c_42,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.03  
% 3.70/1.03  ------  iProver source info
% 3.70/1.03  
% 3.70/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.03  git: non_committed_changes: false
% 3.70/1.03  git: last_make_outside_of_git: false
% 3.70/1.03  
% 3.70/1.03  ------ 
% 3.70/1.03  
% 3.70/1.03  ------ Input Options
% 3.70/1.03  
% 3.70/1.03  --out_options                           all
% 3.70/1.03  --tptp_safe_out                         true
% 3.70/1.03  --problem_path                          ""
% 3.70/1.03  --include_path                          ""
% 3.70/1.03  --clausifier                            res/vclausify_rel
% 3.70/1.03  --clausifier_options                    --mode clausify
% 3.70/1.03  --stdin                                 false
% 3.70/1.03  --stats_out                             all
% 3.70/1.03  
% 3.70/1.03  ------ General Options
% 3.70/1.03  
% 3.70/1.03  --fof                                   false
% 3.70/1.03  --time_out_real                         305.
% 3.70/1.03  --time_out_virtual                      -1.
% 3.70/1.03  --symbol_type_check                     false
% 3.70/1.03  --clausify_out                          false
% 3.70/1.03  --sig_cnt_out                           false
% 3.70/1.03  --trig_cnt_out                          false
% 3.70/1.03  --trig_cnt_out_tolerance                1.
% 3.70/1.03  --trig_cnt_out_sk_spl                   false
% 3.70/1.03  --abstr_cl_out                          false
% 3.70/1.03  
% 3.70/1.03  ------ Global Options
% 3.70/1.03  
% 3.70/1.03  --schedule                              default
% 3.70/1.03  --add_important_lit                     false
% 3.70/1.03  --prop_solver_per_cl                    1000
% 3.70/1.03  --min_unsat_core                        false
% 3.70/1.03  --soft_assumptions                      false
% 3.70/1.03  --soft_lemma_size                       3
% 3.70/1.03  --prop_impl_unit_size                   0
% 3.70/1.03  --prop_impl_unit                        []
% 3.70/1.03  --share_sel_clauses                     true
% 3.70/1.03  --reset_solvers                         false
% 3.70/1.03  --bc_imp_inh                            [conj_cone]
% 3.70/1.03  --conj_cone_tolerance                   3.
% 3.70/1.03  --extra_neg_conj                        none
% 3.70/1.03  --large_theory_mode                     true
% 3.70/1.03  --prolific_symb_bound                   200
% 3.70/1.03  --lt_threshold                          2000
% 3.70/1.03  --clause_weak_htbl                      true
% 3.70/1.03  --gc_record_bc_elim                     false
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing Options
% 3.70/1.03  
% 3.70/1.03  --preprocessing_flag                    true
% 3.70/1.03  --time_out_prep_mult                    0.1
% 3.70/1.03  --splitting_mode                        input
% 3.70/1.03  --splitting_grd                         true
% 3.70/1.03  --splitting_cvd                         false
% 3.70/1.03  --splitting_cvd_svl                     false
% 3.70/1.03  --splitting_nvd                         32
% 3.70/1.03  --sub_typing                            true
% 3.70/1.03  --prep_gs_sim                           true
% 3.70/1.03  --prep_unflatten                        true
% 3.70/1.03  --prep_res_sim                          true
% 3.70/1.03  --prep_upred                            true
% 3.70/1.03  --prep_sem_filter                       exhaustive
% 3.70/1.03  --prep_sem_filter_out                   false
% 3.70/1.03  --pred_elim                             true
% 3.70/1.03  --res_sim_input                         true
% 3.70/1.03  --eq_ax_congr_red                       true
% 3.70/1.03  --pure_diseq_elim                       true
% 3.70/1.03  --brand_transform                       false
% 3.70/1.03  --non_eq_to_eq                          false
% 3.70/1.03  --prep_def_merge                        true
% 3.70/1.03  --prep_def_merge_prop_impl              false
% 3.70/1.03  --prep_def_merge_mbd                    true
% 3.70/1.03  --prep_def_merge_tr_red                 false
% 3.70/1.03  --prep_def_merge_tr_cl                  false
% 3.70/1.03  --smt_preprocessing                     true
% 3.70/1.03  --smt_ac_axioms                         fast
% 3.70/1.03  --preprocessed_out                      false
% 3.70/1.03  --preprocessed_stats                    false
% 3.70/1.03  
% 3.70/1.03  ------ Abstraction refinement Options
% 3.70/1.03  
% 3.70/1.03  --abstr_ref                             []
% 3.70/1.03  --abstr_ref_prep                        false
% 3.70/1.03  --abstr_ref_until_sat                   false
% 3.70/1.03  --abstr_ref_sig_restrict                funpre
% 3.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.03  --abstr_ref_under                       []
% 3.70/1.03  
% 3.70/1.03  ------ SAT Options
% 3.70/1.03  
% 3.70/1.03  --sat_mode                              false
% 3.70/1.03  --sat_fm_restart_options                ""
% 3.70/1.03  --sat_gr_def                            false
% 3.70/1.03  --sat_epr_types                         true
% 3.70/1.03  --sat_non_cyclic_types                  false
% 3.70/1.03  --sat_finite_models                     false
% 3.70/1.03  --sat_fm_lemmas                         false
% 3.70/1.03  --sat_fm_prep                           false
% 3.70/1.03  --sat_fm_uc_incr                        true
% 3.70/1.03  --sat_out_model                         small
% 3.70/1.03  --sat_out_clauses                       false
% 3.70/1.03  
% 3.70/1.03  ------ QBF Options
% 3.70/1.03  
% 3.70/1.03  --qbf_mode                              false
% 3.70/1.03  --qbf_elim_univ                         false
% 3.70/1.03  --qbf_dom_inst                          none
% 3.70/1.03  --qbf_dom_pre_inst                      false
% 3.70/1.03  --qbf_sk_in                             false
% 3.70/1.03  --qbf_pred_elim                         true
% 3.70/1.03  --qbf_split                             512
% 3.70/1.03  
% 3.70/1.03  ------ BMC1 Options
% 3.70/1.03  
% 3.70/1.03  --bmc1_incremental                      false
% 3.70/1.03  --bmc1_axioms                           reachable_all
% 3.70/1.03  --bmc1_min_bound                        0
% 3.70/1.03  --bmc1_max_bound                        -1
% 3.70/1.03  --bmc1_max_bound_default                -1
% 3.70/1.03  --bmc1_symbol_reachability              true
% 3.70/1.03  --bmc1_property_lemmas                  false
% 3.70/1.03  --bmc1_k_induction                      false
% 3.70/1.03  --bmc1_non_equiv_states                 false
% 3.70/1.03  --bmc1_deadlock                         false
% 3.70/1.03  --bmc1_ucm                              false
% 3.70/1.03  --bmc1_add_unsat_core                   none
% 3.70/1.03  --bmc1_unsat_core_children              false
% 3.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.03  --bmc1_out_stat                         full
% 3.70/1.03  --bmc1_ground_init                      false
% 3.70/1.03  --bmc1_pre_inst_next_state              false
% 3.70/1.03  --bmc1_pre_inst_state                   false
% 3.70/1.03  --bmc1_pre_inst_reach_state             false
% 3.70/1.03  --bmc1_out_unsat_core                   false
% 3.70/1.03  --bmc1_aig_witness_out                  false
% 3.70/1.03  --bmc1_verbose                          false
% 3.70/1.03  --bmc1_dump_clauses_tptp                false
% 3.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.03  --bmc1_dump_file                        -
% 3.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.03  --bmc1_ucm_extend_mode                  1
% 3.70/1.03  --bmc1_ucm_init_mode                    2
% 3.70/1.03  --bmc1_ucm_cone_mode                    none
% 3.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.03  --bmc1_ucm_relax_model                  4
% 3.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.03  --bmc1_ucm_layered_model                none
% 3.70/1.03  --bmc1_ucm_max_lemma_size               10
% 3.70/1.03  
% 3.70/1.03  ------ AIG Options
% 3.70/1.03  
% 3.70/1.03  --aig_mode                              false
% 3.70/1.03  
% 3.70/1.03  ------ Instantiation Options
% 3.70/1.03  
% 3.70/1.03  --instantiation_flag                    true
% 3.70/1.03  --inst_sos_flag                         false
% 3.70/1.03  --inst_sos_phase                        true
% 3.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.03  --inst_lit_sel_side                     num_symb
% 3.70/1.03  --inst_solver_per_active                1400
% 3.70/1.03  --inst_solver_calls_frac                1.
% 3.70/1.03  --inst_passive_queue_type               priority_queues
% 3.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.03  --inst_passive_queues_freq              [25;2]
% 3.70/1.03  --inst_dismatching                      true
% 3.70/1.03  --inst_eager_unprocessed_to_passive     true
% 3.70/1.03  --inst_prop_sim_given                   true
% 3.70/1.03  --inst_prop_sim_new                     false
% 3.70/1.03  --inst_subs_new                         false
% 3.70/1.03  --inst_eq_res_simp                      false
% 3.70/1.03  --inst_subs_given                       false
% 3.70/1.03  --inst_orphan_elimination               true
% 3.70/1.03  --inst_learning_loop_flag               true
% 3.70/1.03  --inst_learning_start                   3000
% 3.70/1.03  --inst_learning_factor                  2
% 3.70/1.03  --inst_start_prop_sim_after_learn       3
% 3.70/1.03  --inst_sel_renew                        solver
% 3.70/1.03  --inst_lit_activity_flag                true
% 3.70/1.03  --inst_restr_to_given                   false
% 3.70/1.03  --inst_activity_threshold               500
% 3.70/1.03  --inst_out_proof                        true
% 3.70/1.03  
% 3.70/1.03  ------ Resolution Options
% 3.70/1.03  
% 3.70/1.03  --resolution_flag                       true
% 3.70/1.03  --res_lit_sel                           adaptive
% 3.70/1.03  --res_lit_sel_side                      none
% 3.70/1.03  --res_ordering                          kbo
% 3.70/1.03  --res_to_prop_solver                    active
% 3.70/1.03  --res_prop_simpl_new                    false
% 3.70/1.03  --res_prop_simpl_given                  true
% 3.70/1.03  --res_passive_queue_type                priority_queues
% 3.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.03  --res_passive_queues_freq               [15;5]
% 3.70/1.03  --res_forward_subs                      full
% 3.70/1.03  --res_backward_subs                     full
% 3.70/1.03  --res_forward_subs_resolution           true
% 3.70/1.03  --res_backward_subs_resolution          true
% 3.70/1.03  --res_orphan_elimination                true
% 3.70/1.03  --res_time_limit                        2.
% 3.70/1.03  --res_out_proof                         true
% 3.70/1.03  
% 3.70/1.03  ------ Superposition Options
% 3.70/1.03  
% 3.70/1.03  --superposition_flag                    true
% 3.70/1.03  --sup_passive_queue_type                priority_queues
% 3.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.03  --demod_completeness_check              fast
% 3.70/1.03  --demod_use_ground                      true
% 3.70/1.03  --sup_to_prop_solver                    passive
% 3.70/1.03  --sup_prop_simpl_new                    true
% 3.70/1.03  --sup_prop_simpl_given                  true
% 3.70/1.03  --sup_fun_splitting                     false
% 3.70/1.03  --sup_smt_interval                      50000
% 3.70/1.03  
% 3.70/1.03  ------ Superposition Simplification Setup
% 3.70/1.03  
% 3.70/1.03  --sup_indices_passive                   []
% 3.70/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.03  --sup_full_bw                           [BwDemod]
% 3.70/1.03  --sup_immed_triv                        [TrivRules]
% 3.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.03  --sup_immed_bw_main                     []
% 3.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.03  
% 3.70/1.03  ------ Combination Options
% 3.70/1.03  
% 3.70/1.03  --comb_res_mult                         3
% 3.70/1.03  --comb_sup_mult                         2
% 3.70/1.03  --comb_inst_mult                        10
% 3.70/1.03  
% 3.70/1.03  ------ Debug Options
% 3.70/1.03  
% 3.70/1.03  --dbg_backtrace                         false
% 3.70/1.03  --dbg_dump_prop_clauses                 false
% 3.70/1.03  --dbg_dump_prop_clauses_file            -
% 3.70/1.03  --dbg_out_stat                          false
% 3.70/1.03  ------ Parsing...
% 3.70/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  ------ Proving...
% 3.70/1.03  ------ Problem Properties 
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  clauses                                 22
% 3.70/1.03  conjectures                             3
% 3.70/1.03  EPR                                     2
% 3.70/1.03  Horn                                    17
% 3.70/1.03  unary                                   11
% 3.70/1.03  binary                                  5
% 3.70/1.03  lits                                    44
% 3.70/1.03  lits eq                                 21
% 3.70/1.03  fd_pure                                 0
% 3.70/1.03  fd_pseudo                               0
% 3.70/1.03  fd_cond                                 0
% 3.70/1.03  fd_pseudo_cond                          5
% 3.70/1.03  AC symbols                              0
% 3.70/1.03  
% 3.70/1.03  ------ Schedule dynamic 5 is on 
% 3.70/1.03  
% 3.70/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ 
% 3.70/1.03  Current options:
% 3.70/1.03  ------ 
% 3.70/1.03  
% 3.70/1.03  ------ Input Options
% 3.70/1.03  
% 3.70/1.03  --out_options                           all
% 3.70/1.03  --tptp_safe_out                         true
% 3.70/1.03  --problem_path                          ""
% 3.70/1.03  --include_path                          ""
% 3.70/1.03  --clausifier                            res/vclausify_rel
% 3.70/1.03  --clausifier_options                    --mode clausify
% 3.70/1.03  --stdin                                 false
% 3.70/1.03  --stats_out                             all
% 3.70/1.03  
% 3.70/1.03  ------ General Options
% 3.70/1.03  
% 3.70/1.03  --fof                                   false
% 3.70/1.03  --time_out_real                         305.
% 3.70/1.03  --time_out_virtual                      -1.
% 3.70/1.03  --symbol_type_check                     false
% 3.70/1.03  --clausify_out                          false
% 3.70/1.03  --sig_cnt_out                           false
% 3.70/1.03  --trig_cnt_out                          false
% 3.70/1.03  --trig_cnt_out_tolerance                1.
% 3.70/1.03  --trig_cnt_out_sk_spl                   false
% 3.70/1.03  --abstr_cl_out                          false
% 3.70/1.03  
% 3.70/1.03  ------ Global Options
% 3.70/1.03  
% 3.70/1.03  --schedule                              default
% 3.70/1.03  --add_important_lit                     false
% 3.70/1.03  --prop_solver_per_cl                    1000
% 3.70/1.03  --min_unsat_core                        false
% 3.70/1.03  --soft_assumptions                      false
% 3.70/1.03  --soft_lemma_size                       3
% 3.70/1.03  --prop_impl_unit_size                   0
% 3.70/1.03  --prop_impl_unit                        []
% 3.70/1.03  --share_sel_clauses                     true
% 3.70/1.03  --reset_solvers                         false
% 3.70/1.03  --bc_imp_inh                            [conj_cone]
% 3.70/1.03  --conj_cone_tolerance                   3.
% 3.70/1.03  --extra_neg_conj                        none
% 3.70/1.03  --large_theory_mode                     true
% 3.70/1.03  --prolific_symb_bound                   200
% 3.70/1.03  --lt_threshold                          2000
% 3.70/1.03  --clause_weak_htbl                      true
% 3.70/1.03  --gc_record_bc_elim                     false
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing Options
% 3.70/1.03  
% 3.70/1.03  --preprocessing_flag                    true
% 3.70/1.03  --time_out_prep_mult                    0.1
% 3.70/1.03  --splitting_mode                        input
% 3.70/1.03  --splitting_grd                         true
% 3.70/1.03  --splitting_cvd                         false
% 3.70/1.03  --splitting_cvd_svl                     false
% 3.70/1.03  --splitting_nvd                         32
% 3.70/1.03  --sub_typing                            true
% 3.70/1.03  --prep_gs_sim                           true
% 3.70/1.03  --prep_unflatten                        true
% 3.70/1.03  --prep_res_sim                          true
% 3.70/1.03  --prep_upred                            true
% 3.70/1.03  --prep_sem_filter                       exhaustive
% 3.70/1.03  --prep_sem_filter_out                   false
% 3.70/1.03  --pred_elim                             true
% 3.70/1.03  --res_sim_input                         true
% 3.70/1.03  --eq_ax_congr_red                       true
% 3.70/1.04  --pure_diseq_elim                       true
% 3.70/1.04  --brand_transform                       false
% 3.70/1.04  --non_eq_to_eq                          false
% 3.70/1.04  --prep_def_merge                        true
% 3.70/1.04  --prep_def_merge_prop_impl              false
% 3.70/1.04  --prep_def_merge_mbd                    true
% 3.70/1.04  --prep_def_merge_tr_red                 false
% 3.70/1.04  --prep_def_merge_tr_cl                  false
% 3.70/1.04  --smt_preprocessing                     true
% 3.70/1.04  --smt_ac_axioms                         fast
% 3.70/1.04  --preprocessed_out                      false
% 3.70/1.04  --preprocessed_stats                    false
% 3.70/1.04  
% 3.70/1.04  ------ Abstraction refinement Options
% 3.70/1.04  
% 3.70/1.04  --abstr_ref                             []
% 3.70/1.04  --abstr_ref_prep                        false
% 3.70/1.04  --abstr_ref_until_sat                   false
% 3.70/1.04  --abstr_ref_sig_restrict                funpre
% 3.70/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.04  --abstr_ref_under                       []
% 3.70/1.04  
% 3.70/1.04  ------ SAT Options
% 3.70/1.04  
% 3.70/1.04  --sat_mode                              false
% 3.70/1.04  --sat_fm_restart_options                ""
% 3.70/1.04  --sat_gr_def                            false
% 3.70/1.04  --sat_epr_types                         true
% 3.70/1.04  --sat_non_cyclic_types                  false
% 3.70/1.04  --sat_finite_models                     false
% 3.70/1.04  --sat_fm_lemmas                         false
% 3.70/1.04  --sat_fm_prep                           false
% 3.70/1.04  --sat_fm_uc_incr                        true
% 3.70/1.04  --sat_out_model                         small
% 3.70/1.04  --sat_out_clauses                       false
% 3.70/1.04  
% 3.70/1.04  ------ QBF Options
% 3.70/1.04  
% 3.70/1.04  --qbf_mode                              false
% 3.70/1.04  --qbf_elim_univ                         false
% 3.70/1.04  --qbf_dom_inst                          none
% 3.70/1.04  --qbf_dom_pre_inst                      false
% 3.70/1.04  --qbf_sk_in                             false
% 3.70/1.04  --qbf_pred_elim                         true
% 3.70/1.04  --qbf_split                             512
% 3.70/1.04  
% 3.70/1.04  ------ BMC1 Options
% 3.70/1.04  
% 3.70/1.04  --bmc1_incremental                      false
% 3.70/1.04  --bmc1_axioms                           reachable_all
% 3.70/1.04  --bmc1_min_bound                        0
% 3.70/1.04  --bmc1_max_bound                        -1
% 3.70/1.04  --bmc1_max_bound_default                -1
% 3.70/1.04  --bmc1_symbol_reachability              true
% 3.70/1.04  --bmc1_property_lemmas                  false
% 3.70/1.04  --bmc1_k_induction                      false
% 3.70/1.04  --bmc1_non_equiv_states                 false
% 3.70/1.04  --bmc1_deadlock                         false
% 3.70/1.04  --bmc1_ucm                              false
% 3.70/1.04  --bmc1_add_unsat_core                   none
% 3.70/1.04  --bmc1_unsat_core_children              false
% 3.70/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.04  --bmc1_out_stat                         full
% 3.70/1.04  --bmc1_ground_init                      false
% 3.70/1.04  --bmc1_pre_inst_next_state              false
% 3.70/1.04  --bmc1_pre_inst_state                   false
% 3.70/1.04  --bmc1_pre_inst_reach_state             false
% 3.70/1.04  --bmc1_out_unsat_core                   false
% 3.70/1.04  --bmc1_aig_witness_out                  false
% 3.70/1.04  --bmc1_verbose                          false
% 3.70/1.04  --bmc1_dump_clauses_tptp                false
% 3.70/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.04  --bmc1_dump_file                        -
% 3.70/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.04  --bmc1_ucm_extend_mode                  1
% 3.70/1.04  --bmc1_ucm_init_mode                    2
% 3.70/1.04  --bmc1_ucm_cone_mode                    none
% 3.70/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.04  --bmc1_ucm_relax_model                  4
% 3.70/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.04  --bmc1_ucm_layered_model                none
% 3.70/1.04  --bmc1_ucm_max_lemma_size               10
% 3.70/1.04  
% 3.70/1.04  ------ AIG Options
% 3.70/1.04  
% 3.70/1.04  --aig_mode                              false
% 3.70/1.04  
% 3.70/1.04  ------ Instantiation Options
% 3.70/1.04  
% 3.70/1.04  --instantiation_flag                    true
% 3.70/1.04  --inst_sos_flag                         false
% 3.70/1.04  --inst_sos_phase                        true
% 3.70/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.04  --inst_lit_sel_side                     none
% 3.70/1.04  --inst_solver_per_active                1400
% 3.70/1.04  --inst_solver_calls_frac                1.
% 3.70/1.04  --inst_passive_queue_type               priority_queues
% 3.70/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.04  --inst_passive_queues_freq              [25;2]
% 3.70/1.04  --inst_dismatching                      true
% 3.70/1.04  --inst_eager_unprocessed_to_passive     true
% 3.70/1.04  --inst_prop_sim_given                   true
% 3.70/1.04  --inst_prop_sim_new                     false
% 3.70/1.04  --inst_subs_new                         false
% 3.70/1.04  --inst_eq_res_simp                      false
% 3.70/1.04  --inst_subs_given                       false
% 3.70/1.04  --inst_orphan_elimination               true
% 3.70/1.04  --inst_learning_loop_flag               true
% 3.70/1.04  --inst_learning_start                   3000
% 3.70/1.04  --inst_learning_factor                  2
% 3.70/1.04  --inst_start_prop_sim_after_learn       3
% 3.70/1.04  --inst_sel_renew                        solver
% 3.70/1.04  --inst_lit_activity_flag                true
% 3.70/1.04  --inst_restr_to_given                   false
% 3.70/1.04  --inst_activity_threshold               500
% 3.70/1.04  --inst_out_proof                        true
% 3.70/1.04  
% 3.70/1.04  ------ Resolution Options
% 3.70/1.04  
% 3.70/1.04  --resolution_flag                       false
% 3.70/1.04  --res_lit_sel                           adaptive
% 3.70/1.04  --res_lit_sel_side                      none
% 3.70/1.04  --res_ordering                          kbo
% 3.70/1.04  --res_to_prop_solver                    active
% 3.70/1.04  --res_prop_simpl_new                    false
% 3.70/1.04  --res_prop_simpl_given                  true
% 3.70/1.04  --res_passive_queue_type                priority_queues
% 3.70/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.04  --res_passive_queues_freq               [15;5]
% 3.70/1.04  --res_forward_subs                      full
% 3.70/1.04  --res_backward_subs                     full
% 3.70/1.04  --res_forward_subs_resolution           true
% 3.70/1.04  --res_backward_subs_resolution          true
% 3.70/1.04  --res_orphan_elimination                true
% 3.70/1.04  --res_time_limit                        2.
% 3.70/1.04  --res_out_proof                         true
% 3.70/1.04  
% 3.70/1.04  ------ Superposition Options
% 3.70/1.04  
% 3.70/1.04  --superposition_flag                    true
% 3.70/1.04  --sup_passive_queue_type                priority_queues
% 3.70/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.04  --demod_completeness_check              fast
% 3.70/1.04  --demod_use_ground                      true
% 3.70/1.04  --sup_to_prop_solver                    passive
% 3.70/1.04  --sup_prop_simpl_new                    true
% 3.70/1.04  --sup_prop_simpl_given                  true
% 3.70/1.04  --sup_fun_splitting                     false
% 3.70/1.04  --sup_smt_interval                      50000
% 3.70/1.04  
% 3.70/1.04  ------ Superposition Simplification Setup
% 3.70/1.04  
% 3.70/1.04  --sup_indices_passive                   []
% 3.70/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.04  --sup_full_bw                           [BwDemod]
% 3.70/1.04  --sup_immed_triv                        [TrivRules]
% 3.70/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.04  --sup_immed_bw_main                     []
% 3.70/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.04  
% 3.70/1.04  ------ Combination Options
% 3.70/1.04  
% 3.70/1.04  --comb_res_mult                         3
% 3.70/1.04  --comb_sup_mult                         2
% 3.70/1.04  --comb_inst_mult                        10
% 3.70/1.04  
% 3.70/1.04  ------ Debug Options
% 3.70/1.04  
% 3.70/1.04  --dbg_backtrace                         false
% 3.70/1.04  --dbg_dump_prop_clauses                 false
% 3.70/1.04  --dbg_dump_prop_clauses_file            -
% 3.70/1.04  --dbg_out_stat                          false
% 3.70/1.04  
% 3.70/1.04  
% 3.70/1.04  
% 3.70/1.04  
% 3.70/1.04  ------ Proving...
% 3.70/1.04  
% 3.70/1.04  
% 3.70/1.04  % SZS status Theorem for theBenchmark.p
% 3.70/1.04  
% 3.70/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.04  
% 3.70/1.04  fof(f15,axiom,(
% 3.70/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f24,plain,(
% 3.70/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.70/1.04    inference(ennf_transformation,[],[f15])).
% 3.70/1.04  
% 3.70/1.04  fof(f33,plain,(
% 3.70/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.70/1.04    inference(nnf_transformation,[],[f24])).
% 3.70/1.04  
% 3.70/1.04  fof(f34,plain,(
% 3.70/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.70/1.04    inference(flattening,[],[f33])).
% 3.70/1.04  
% 3.70/1.04  fof(f60,plain,(
% 3.70/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.70/1.04    inference(cnf_transformation,[],[f34])).
% 3.70/1.04  
% 3.70/1.04  fof(f7,axiom,(
% 3.70/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f50,plain,(
% 3.70/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f7])).
% 3.70/1.04  
% 3.70/1.04  fof(f8,axiom,(
% 3.70/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f51,plain,(
% 3.70/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f8])).
% 3.70/1.04  
% 3.70/1.04  fof(f9,axiom,(
% 3.70/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f52,plain,(
% 3.70/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f9])).
% 3.70/1.04  
% 3.70/1.04  fof(f10,axiom,(
% 3.70/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f53,plain,(
% 3.70/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f10])).
% 3.70/1.04  
% 3.70/1.04  fof(f11,axiom,(
% 3.70/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f54,plain,(
% 3.70/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f11])).
% 3.70/1.04  
% 3.70/1.04  fof(f12,axiom,(
% 3.70/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f55,plain,(
% 3.70/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f12])).
% 3.70/1.04  
% 3.70/1.04  fof(f13,axiom,(
% 3.70/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f56,plain,(
% 3.70/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f13])).
% 3.70/1.04  
% 3.70/1.04  fof(f66,plain,(
% 3.70/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f55,f56])).
% 3.70/1.04  
% 3.70/1.04  fof(f67,plain,(
% 3.70/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f54,f66])).
% 3.70/1.04  
% 3.70/1.04  fof(f68,plain,(
% 3.70/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f53,f67])).
% 3.70/1.04  
% 3.70/1.04  fof(f69,plain,(
% 3.70/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f52,f68])).
% 3.70/1.04  
% 3.70/1.04  fof(f70,plain,(
% 3.70/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f51,f69])).
% 3.70/1.04  
% 3.70/1.04  fof(f71,plain,(
% 3.70/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f50,f70])).
% 3.70/1.04  
% 3.70/1.04  fof(f83,plain,(
% 3.70/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 3.70/1.04    inference(definition_unfolding,[],[f60,f70,f71])).
% 3.70/1.04  
% 3.70/1.04  fof(f96,plain,(
% 3.70/1.04    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.70/1.04    inference(equality_resolution,[],[f83])).
% 3.70/1.04  
% 3.70/1.04  fof(f16,conjecture,(
% 3.70/1.04    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f17,negated_conjecture,(
% 3.70/1.04    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.70/1.04    inference(negated_conjecture,[],[f16])).
% 3.70/1.04  
% 3.70/1.04  fof(f25,plain,(
% 3.70/1.04    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.70/1.04    inference(ennf_transformation,[],[f17])).
% 3.70/1.04  
% 3.70/1.04  fof(f35,plain,(
% 3.70/1.04    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))),
% 3.70/1.04    introduced(choice_axiom,[])).
% 3.70/1.04  
% 3.70/1.04  fof(f36,plain,(
% 3.70/1.04    sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 3.70/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f35])).
% 3.70/1.04  
% 3.70/1.04  fof(f63,plain,(
% 3.70/1.04    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 3.70/1.04    inference(cnf_transformation,[],[f36])).
% 3.70/1.04  
% 3.70/1.04  fof(f86,plain,(
% 3.70/1.04    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 3.70/1.04    inference(definition_unfolding,[],[f63,f70,f70])).
% 3.70/1.04  
% 3.70/1.04  fof(f5,axiom,(
% 3.70/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f21,plain,(
% 3.70/1.04    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.70/1.04    inference(ennf_transformation,[],[f5])).
% 3.70/1.04  
% 3.70/1.04  fof(f41,plain,(
% 3.70/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f21])).
% 3.70/1.04  
% 3.70/1.04  fof(f1,axiom,(
% 3.70/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f37,plain,(
% 3.70/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f1])).
% 3.70/1.04  
% 3.70/1.04  fof(f4,axiom,(
% 3.70/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f20,plain,(
% 3.70/1.04    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.70/1.04    inference(ennf_transformation,[],[f4])).
% 3.70/1.04  
% 3.70/1.04  fof(f40,plain,(
% 3.70/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.70/1.04    inference(cnf_transformation,[],[f20])).
% 3.70/1.04  
% 3.70/1.04  fof(f3,axiom,(
% 3.70/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f18,plain,(
% 3.70/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.70/1.04    inference(rectify,[],[f3])).
% 3.70/1.04  
% 3.70/1.04  fof(f19,plain,(
% 3.70/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.70/1.04    inference(ennf_transformation,[],[f18])).
% 3.70/1.04  
% 3.70/1.04  fof(f26,plain,(
% 3.70/1.04    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.70/1.04    introduced(choice_axiom,[])).
% 3.70/1.04  
% 3.70/1.04  fof(f27,plain,(
% 3.70/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.70/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).
% 3.70/1.04  
% 3.70/1.04  fof(f39,plain,(
% 3.70/1.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.70/1.04    inference(cnf_transformation,[],[f27])).
% 3.70/1.04  
% 3.70/1.04  fof(f14,axiom,(
% 3.70/1.04    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f23,plain,(
% 3.70/1.04    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.70/1.04    inference(ennf_transformation,[],[f14])).
% 3.70/1.04  
% 3.70/1.04  fof(f57,plain,(
% 3.70/1.04    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.70/1.04    inference(cnf_transformation,[],[f23])).
% 3.70/1.04  
% 3.70/1.04  fof(f80,plain,(
% 3.70/1.04    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.70/1.04    inference(definition_unfolding,[],[f57,f71])).
% 3.70/1.04  
% 3.70/1.04  fof(f6,axiom,(
% 3.70/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.70/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.04  
% 3.70/1.04  fof(f22,plain,(
% 3.70/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.70/1.04    inference(ennf_transformation,[],[f6])).
% 3.70/1.04  
% 3.70/1.04  fof(f28,plain,(
% 3.70/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.04    inference(nnf_transformation,[],[f22])).
% 3.70/1.04  
% 3.70/1.04  fof(f29,plain,(
% 3.70/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.04    inference(flattening,[],[f28])).
% 3.70/1.04  
% 3.70/1.04  fof(f30,plain,(
% 3.70/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.04    inference(rectify,[],[f29])).
% 3.70/1.04  
% 3.70/1.04  fof(f31,plain,(
% 3.70/1.04    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.70/1.04    introduced(choice_axiom,[])).
% 3.70/1.04  
% 3.70/1.04  fof(f32,plain,(
% 3.70/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.70/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.70/1.04  
% 3.70/1.04  fof(f42,plain,(
% 3.70/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.70/1.04    inference(cnf_transformation,[],[f32])).
% 3.70/1.04  
% 3.70/1.04  fof(f79,plain,(
% 3.70/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.70/1.04    inference(definition_unfolding,[],[f42,f69])).
% 3.70/1.04  
% 3.70/1.04  fof(f93,plain,(
% 3.70/1.04    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.70/1.04    inference(equality_resolution,[],[f79])).
% 3.70/1.04  
% 3.70/1.04  fof(f43,plain,(
% 3.70/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.70/1.04    inference(cnf_transformation,[],[f32])).
% 3.70/1.04  
% 3.70/1.04  fof(f78,plain,(
% 3.70/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.70/1.04    inference(definition_unfolding,[],[f43,f69])).
% 3.70/1.04  
% 3.70/1.04  fof(f91,plain,(
% 3.70/1.04    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.70/1.04    inference(equality_resolution,[],[f78])).
% 3.70/1.04  
% 3.70/1.04  fof(f92,plain,(
% 3.70/1.04    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 3.70/1.04    inference(equality_resolution,[],[f91])).
% 3.70/1.04  
% 3.70/1.04  fof(f65,plain,(
% 3.70/1.04    sK2 != sK5),
% 3.70/1.04    inference(cnf_transformation,[],[f36])).
% 3.70/1.04  
% 3.70/1.04  fof(f64,plain,(
% 3.70/1.04    sK2 != sK4),
% 3.70/1.04    inference(cnf_transformation,[],[f36])).
% 3.70/1.04  
% 3.70/1.04  cnf(c_16,plain,
% 3.70/1.04      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.70/1.04      inference(cnf_transformation,[],[f96]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1018,plain,
% 3.70/1.04      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_21,negated_conjecture,
% 3.70/1.04      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 3.70/1.04      inference(cnf_transformation,[],[f86]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1015,plain,
% 3.70/1.04      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_4,plain,
% 3.70/1.04      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.70/1.04      inference(cnf_transformation,[],[f41]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1030,plain,
% 3.70/1.04      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1221,plain,
% 3.70/1.04      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 3.70/1.04      inference(superposition,[status(thm)],[c_1015,c_1030]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_0,plain,
% 3.70/1.04      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.70/1.04      inference(cnf_transformation,[],[f37]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_3,plain,
% 3.70/1.04      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 3.70/1.04      inference(cnf_transformation,[],[f40]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1031,plain,
% 3.70/1.04      ( r1_tarski(X0,X1) = iProver_top
% 3.70/1.04      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1776,plain,
% 3.70/1.04      ( r1_tarski(X0,X1) = iProver_top
% 3.70/1.04      | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.70/1.04      inference(superposition,[status(thm)],[c_0,c_1031]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1875,plain,
% 3.70/1.04      ( r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top
% 3.70/1.04      | r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 3.70/1.04      inference(superposition,[status(thm)],[c_1221,c_1776]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_2739,plain,
% 3.70/1.04      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 3.70/1.04      inference(superposition,[status(thm)],[c_1018,c_1875]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_3433,plain,
% 3.70/1.04      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.70/1.04      inference(superposition,[status(thm)],[c_2739,c_1030]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1,plain,
% 3.70/1.04      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.70/1.04      inference(cnf_transformation,[],[f39]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1033,plain,
% 3.70/1.04      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.70/1.04      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_8166,plain,
% 3.70/1.04      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.70/1.04      | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
% 3.70/1.04      inference(superposition,[status(thm)],[c_3433,c_1033]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_8202,plain,
% 3.70/1.04      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.70/1.04      | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
% 3.70/1.04      inference(instantiation,[status(thm)],[c_8166]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_13,plain,
% 3.70/1.04      ( r2_hidden(X0,X1)
% 3.70/1.04      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.70/1.04      inference(cnf_transformation,[],[f80]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_2809,plain,
% 3.70/1.04      ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
% 3.70/1.04      | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 3.70/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_2810,plain,
% 3.70/1.04      ( r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top
% 3.70/1.04      | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_2809]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_12,plain,
% 3.70/1.04      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 3.70/1.04      | X0 = X1
% 3.70/1.04      | X0 = X2
% 3.70/1.04      | X0 = X3 ),
% 3.70/1.04      inference(cnf_transformation,[],[f93]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1190,plain,
% 3.70/1.04      ( ~ r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0,X1))
% 3.70/1.04      | sK2 = X0
% 3.70/1.04      | sK2 = X1
% 3.70/1.04      | sK2 = sK4 ),
% 3.70/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1313,plain,
% 3.70/1.04      ( ~ r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))
% 3.70/1.04      | sK2 = X0
% 3.70/1.04      | sK2 = sK4 ),
% 3.70/1.04      inference(instantiation,[status(thm)],[c_1190]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1802,plain,
% 3.70/1.04      ( ~ r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
% 3.70/1.04      | sK2 = sK4
% 3.70/1.04      | sK2 = sK5 ),
% 3.70/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_1803,plain,
% 3.70/1.04      ( sK2 = sK4
% 3.70/1.04      | sK2 = sK5
% 3.70/1.04      | r2_hidden(sK2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_11,plain,
% 3.70/1.04      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 3.70/1.04      inference(cnf_transformation,[],[f92]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_40,plain,
% 3.70/1.04      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 3.70/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_42,plain,
% 3.70/1.04      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.70/1.04      inference(instantiation,[status(thm)],[c_40]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_19,negated_conjecture,
% 3.70/1.04      ( sK2 != sK5 ),
% 3.70/1.04      inference(cnf_transformation,[],[f65]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(c_20,negated_conjecture,
% 3.70/1.04      ( sK2 != sK4 ),
% 3.70/1.04      inference(cnf_transformation,[],[f64]) ).
% 3.70/1.04  
% 3.70/1.04  cnf(contradiction,plain,
% 3.70/1.04      ( $false ),
% 3.70/1.04      inference(minisat,
% 3.70/1.04                [status(thm)],
% 3.70/1.04                [c_8202,c_2810,c_1803,c_42,c_19,c_20]) ).
% 3.70/1.04  
% 3.70/1.04  
% 3.70/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.04  
% 3.70/1.04  ------                               Statistics
% 3.70/1.04  
% 3.70/1.04  ------ General
% 3.70/1.04  
% 3.70/1.04  abstr_ref_over_cycles:                  0
% 3.70/1.04  abstr_ref_under_cycles:                 0
% 3.70/1.04  gc_basic_clause_elim:                   0
% 3.70/1.04  forced_gc_time:                         0
% 3.70/1.04  parsing_time:                           0.021
% 3.70/1.04  unif_index_cands_time:                  0.
% 3.70/1.04  unif_index_add_time:                    0.
% 3.70/1.04  orderings_time:                         0.
% 3.70/1.04  out_proof_time:                         0.011
% 3.70/1.04  total_time:                             0.389
% 3.70/1.04  num_of_symbols:                         43
% 3.70/1.04  num_of_terms:                           8164
% 3.70/1.04  
% 3.70/1.04  ------ Preprocessing
% 3.70/1.04  
% 3.70/1.04  num_of_splits:                          0
% 3.70/1.04  num_of_split_atoms:                     0
% 3.70/1.04  num_of_reused_defs:                     0
% 3.70/1.04  num_eq_ax_congr_red:                    18
% 3.70/1.04  num_of_sem_filtered_clauses:            1
% 3.70/1.04  num_of_subtypes:                        0
% 3.70/1.04  monotx_restored_types:                  0
% 3.70/1.04  sat_num_of_epr_types:                   0
% 3.70/1.04  sat_num_of_non_cyclic_types:            0
% 3.70/1.04  sat_guarded_non_collapsed_types:        0
% 3.70/1.04  num_pure_diseq_elim:                    0
% 3.70/1.04  simp_replaced_by:                       0
% 3.70/1.04  res_preprocessed:                       79
% 3.70/1.04  prep_upred:                             0
% 3.70/1.04  prep_unflattend:                        38
% 3.70/1.04  smt_new_axioms:                         0
% 3.70/1.04  pred_elim_cands:                        3
% 3.70/1.04  pred_elim:                              0
% 3.70/1.04  pred_elim_cl:                           0
% 3.70/1.04  pred_elim_cycles:                       2
% 3.70/1.04  merged_defs:                            0
% 3.70/1.04  merged_defs_ncl:                        0
% 3.70/1.04  bin_hyper_res:                          0
% 3.70/1.04  prep_cycles:                            3
% 3.70/1.04  pred_elim_time:                         0.008
% 3.70/1.04  splitting_time:                         0.
% 3.70/1.04  sem_filter_time:                        0.
% 3.70/1.04  monotx_time:                            0.
% 3.70/1.04  subtype_inf_time:                       0.
% 3.70/1.04  
% 3.70/1.04  ------ Problem properties
% 3.70/1.04  
% 3.70/1.04  clauses:                                22
% 3.70/1.04  conjectures:                            3
% 3.70/1.04  epr:                                    2
% 3.70/1.04  horn:                                   17
% 3.70/1.04  ground:                                 3
% 3.70/1.04  unary:                                  11
% 3.70/1.04  binary:                                 5
% 3.70/1.04  lits:                                   44
% 3.70/1.04  lits_eq:                                21
% 3.70/1.04  fd_pure:                                0
% 3.70/1.04  fd_pseudo:                              0
% 3.70/1.04  fd_cond:                                0
% 3.70/1.04  fd_pseudo_cond:                         5
% 3.70/1.04  ac_symbols:                             0
% 3.70/1.04  
% 3.70/1.04  ------ Propositional Solver
% 3.70/1.04  
% 3.70/1.04  prop_solver_calls:                      23
% 3.70/1.04  prop_fast_solver_calls:                 697
% 3.70/1.04  smt_solver_calls:                       0
% 3.70/1.04  smt_fast_solver_calls:                  0
% 3.70/1.04  prop_num_of_clauses:                    2892
% 3.70/1.04  prop_preprocess_simplified:             7406
% 3.70/1.04  prop_fo_subsumed:                       21
% 3.70/1.04  prop_solver_time:                       0.
% 3.70/1.04  smt_solver_time:                        0.
% 3.70/1.04  smt_fast_solver_time:                   0.
% 3.70/1.04  prop_fast_solver_time:                  0.
% 3.70/1.04  prop_unsat_core_time:                   0.
% 3.70/1.04  
% 3.70/1.04  ------ QBF
% 3.70/1.04  
% 3.70/1.04  qbf_q_res:                              0
% 3.70/1.04  qbf_num_tautologies:                    0
% 3.70/1.04  qbf_prep_cycles:                        0
% 3.70/1.04  
% 3.70/1.04  ------ BMC1
% 3.70/1.04  
% 3.70/1.04  bmc1_current_bound:                     -1
% 3.70/1.04  bmc1_last_solved_bound:                 -1
% 3.70/1.04  bmc1_unsat_core_size:                   -1
% 3.70/1.04  bmc1_unsat_core_parents_size:           -1
% 3.70/1.04  bmc1_merge_next_fun:                    0
% 3.70/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.04  
% 3.70/1.04  ------ Instantiation
% 3.70/1.04  
% 3.70/1.04  inst_num_of_clauses:                    871
% 3.70/1.04  inst_num_in_passive:                    227
% 3.70/1.04  inst_num_in_active:                     313
% 3.70/1.04  inst_num_in_unprocessed:                331
% 3.70/1.04  inst_num_of_loops:                      400
% 3.70/1.04  inst_num_of_learning_restarts:          0
% 3.70/1.04  inst_num_moves_active_passive:          86
% 3.70/1.04  inst_lit_activity:                      0
% 3.70/1.04  inst_lit_activity_moves:                0
% 3.70/1.04  inst_num_tautologies:                   0
% 3.70/1.04  inst_num_prop_implied:                  0
% 3.70/1.04  inst_num_existing_simplified:           0
% 3.70/1.04  inst_num_eq_res_simplified:             0
% 3.70/1.04  inst_num_child_elim:                    0
% 3.70/1.04  inst_num_of_dismatching_blockings:      540
% 3.70/1.04  inst_num_of_non_proper_insts:           770
% 3.70/1.04  inst_num_of_duplicates:                 0
% 3.70/1.04  inst_inst_num_from_inst_to_res:         0
% 3.70/1.04  inst_dismatching_checking_time:         0.
% 3.70/1.04  
% 3.70/1.04  ------ Resolution
% 3.70/1.04  
% 3.70/1.04  res_num_of_clauses:                     0
% 3.70/1.04  res_num_in_passive:                     0
% 3.70/1.04  res_num_in_active:                      0
% 3.70/1.04  res_num_of_loops:                       82
% 3.70/1.04  res_forward_subset_subsumed:            159
% 3.70/1.04  res_backward_subset_subsumed:           2
% 3.70/1.04  res_forward_subsumed:                   0
% 3.70/1.04  res_backward_subsumed:                  0
% 3.70/1.04  res_forward_subsumption_resolution:     1
% 3.70/1.04  res_backward_subsumption_resolution:    0
% 3.70/1.04  res_clause_to_clause_subsumption:       749
% 3.70/1.04  res_orphan_elimination:                 0
% 3.70/1.04  res_tautology_del:                      23
% 3.70/1.04  res_num_eq_res_simplified:              0
% 3.70/1.04  res_num_sel_changes:                    0
% 3.70/1.04  res_moves_from_active_to_pass:          0
% 3.70/1.04  
% 3.70/1.04  ------ Superposition
% 3.70/1.04  
% 3.70/1.04  sup_time_total:                         0.
% 3.70/1.04  sup_time_generating:                    0.
% 3.70/1.04  sup_time_sim_full:                      0.
% 3.70/1.04  sup_time_sim_immed:                     0.
% 3.70/1.04  
% 3.70/1.04  sup_num_of_clauses:                     117
% 3.70/1.04  sup_num_in_active:                      61
% 3.70/1.04  sup_num_in_passive:                     56
% 3.70/1.04  sup_num_of_loops:                       79
% 3.70/1.04  sup_fw_superposition:                   143
% 3.70/1.04  sup_bw_superposition:                   171
% 3.70/1.04  sup_immediate_simplified:               68
% 3.70/1.04  sup_given_eliminated:                   3
% 3.70/1.04  comparisons_done:                       0
% 3.70/1.04  comparisons_avoided:                    21
% 3.70/1.04  
% 3.70/1.04  ------ Simplifications
% 3.70/1.04  
% 3.70/1.04  
% 3.70/1.04  sim_fw_subset_subsumed:                 36
% 3.70/1.04  sim_bw_subset_subsumed:                 44
% 3.70/1.04  sim_fw_subsumed:                        27
% 3.70/1.04  sim_bw_subsumed:                        11
% 3.70/1.04  sim_fw_subsumption_res:                 0
% 3.70/1.04  sim_bw_subsumption_res:                 0
% 3.70/1.04  sim_tautology_del:                      9
% 3.70/1.04  sim_eq_tautology_del:                   16
% 3.70/1.04  sim_eq_res_simp:                        0
% 3.70/1.04  sim_fw_demodulated:                     4
% 3.70/1.04  sim_bw_demodulated:                     0
% 3.70/1.04  sim_light_normalised:                   0
% 3.70/1.04  sim_joinable_taut:                      0
% 3.70/1.04  sim_joinable_simp:                      0
% 3.70/1.04  sim_ac_normalised:                      0
% 3.70/1.04  sim_smt_subsumption:                    0
% 3.70/1.04  
%------------------------------------------------------------------------------
