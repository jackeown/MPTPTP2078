%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:45 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 162 expanded)
%              Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  302 ( 540 expanded)
%              Number of equality atoms :  156 ( 297 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f73,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f68,f68])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34])).

fof(f65,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f83,plain,(
    r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f65,f69,f70])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f89,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f90,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f89])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f93,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f94,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f66,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8133,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8279,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14,c_8133])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8144,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8509,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3
    | r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_8144])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8142,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10962,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8509,c_8142])).

cnf(c_19,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_8139,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8148,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9041,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_8148])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8147,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9238,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9041,c_8147])).

cnf(c_9509,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8139,c_9238])).

cnf(c_10977,plain,
    ( r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10962,c_9509])).

cnf(c_11032,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10977])).

cnf(c_21,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_37,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_39,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11032,c_39,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.75/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.98  
% 3.75/0.98  ------  iProver source info
% 3.75/0.98  
% 3.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.98  git: non_committed_changes: false
% 3.75/0.98  git: last_make_outside_of_git: false
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  ------ Parsing...
% 3.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  ------ Proving...
% 3.75/0.98  ------ Problem Properties 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  clauses                                 25
% 3.75/0.98  conjectures                             4
% 3.75/0.98  EPR                                     4
% 3.75/0.98  Horn                                    19
% 3.75/0.98  unary                                   9
% 3.75/0.98  binary                                  6
% 3.75/0.98  lits                                    55
% 3.75/0.98  lits eq                                 21
% 3.75/0.98  fd_pure                                 0
% 3.75/0.98  fd_pseudo                               0
% 3.75/0.98  fd_cond                                 0
% 3.75/0.98  fd_pseudo_cond                          8
% 3.75/0.98  AC symbols                              0
% 3.75/0.98  
% 3.75/0.98  ------ Input Options Time Limit: Unbounded
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.75/0.98  Current options:
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS status Theorem for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  fof(f7,axiom,(
% 3.75/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f50,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f7])).
% 3.75/0.98  
% 3.75/0.98  fof(f10,axiom,(
% 3.75/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f60,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f10])).
% 3.75/0.98  
% 3.75/0.98  fof(f11,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f61,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f11])).
% 3.75/0.98  
% 3.75/0.98  fof(f12,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f62,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f12])).
% 3.75/0.98  
% 3.75/0.98  fof(f67,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f61,f62])).
% 3.75/0.98  
% 3.75/0.98  fof(f68,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f60,f67])).
% 3.75/0.98  
% 3.75/0.98  fof(f73,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f50,f68,f68])).
% 3.75/0.98  
% 3.75/0.98  fof(f15,conjecture,(
% 3.75/0.98    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f16,negated_conjecture,(
% 3.75/0.98    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.75/0.98    inference(negated_conjecture,[],[f15])).
% 3.75/0.98  
% 3.75/0.98  fof(f20,plain,(
% 3.75/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.75/0.98    inference(ennf_transformation,[],[f16])).
% 3.75/0.98  
% 3.75/0.98  fof(f34,plain,(
% 3.75/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f35,plain,(
% 3.75/0.98    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34])).
% 3.75/0.98  
% 3.75/0.98  fof(f65,plain,(
% 3.75/0.98    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.75/0.98    inference(cnf_transformation,[],[f35])).
% 3.75/0.98  
% 3.75/0.98  fof(f14,axiom,(
% 3.75/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f64,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f14])).
% 3.75/0.98  
% 3.75/0.98  fof(f69,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f64,f68])).
% 3.75/0.98  
% 3.75/0.98  fof(f9,axiom,(
% 3.75/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f59,plain,(
% 3.75/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f9])).
% 3.75/0.98  
% 3.75/0.98  fof(f70,plain,(
% 3.75/0.98    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f59,f68])).
% 3.75/0.98  
% 3.75/0.98  fof(f83,plain,(
% 3.75/0.98    r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),sK3)),
% 3.75/0.98    inference(definition_unfolding,[],[f65,f69,f70])).
% 3.75/0.98  
% 3.75/0.98  fof(f3,axiom,(
% 3.75/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f26,plain,(
% 3.75/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.98    inference(nnf_transformation,[],[f3])).
% 3.75/0.98  
% 3.75/0.98  fof(f27,plain,(
% 3.75/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.98    inference(flattening,[],[f26])).
% 3.75/0.98  
% 3.75/0.98  fof(f45,plain,(
% 3.75/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f27])).
% 3.75/0.98  
% 3.75/0.98  fof(f5,axiom,(
% 3.75/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f47,plain,(
% 3.75/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f5])).
% 3.75/0.98  
% 3.75/0.98  fof(f72,plain,(
% 3.75/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f47,f69])).
% 3.75/0.98  
% 3.75/0.98  fof(f8,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f18,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.75/0.98    inference(ennf_transformation,[],[f8])).
% 3.75/0.98  
% 3.75/0.98  fof(f29,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.75/0.98    inference(nnf_transformation,[],[f18])).
% 3.75/0.98  
% 3.75/0.98  fof(f30,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.75/0.98    inference(flattening,[],[f29])).
% 3.75/0.98  
% 3.75/0.98  fof(f31,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.75/0.98    inference(rectify,[],[f30])).
% 3.75/0.98  
% 3.75/0.98  fof(f32,plain,(
% 3.75/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f33,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f54,plain,(
% 3.75/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.75/0.98    inference(cnf_transformation,[],[f33])).
% 3.75/0.98  
% 3.75/0.98  fof(f78,plain,(
% 3.75/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.75/0.98    inference(definition_unfolding,[],[f54,f67])).
% 3.75/0.98  
% 3.75/0.98  fof(f89,plain,(
% 3.75/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 3.75/0.98    inference(equality_resolution,[],[f78])).
% 3.75/0.98  
% 3.75/0.98  fof(f90,plain,(
% 3.75/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 3.75/0.98    inference(equality_resolution,[],[f89])).
% 3.75/0.98  
% 3.75/0.98  fof(f4,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f46,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f4])).
% 3.75/0.98  
% 3.75/0.98  fof(f71,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f46,f69])).
% 3.75/0.98  
% 3.75/0.98  fof(f1,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f21,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.75/0.98    inference(nnf_transformation,[],[f1])).
% 3.75/0.98  
% 3.75/0.98  fof(f22,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.75/0.98    inference(flattening,[],[f21])).
% 3.75/0.98  
% 3.75/0.98  fof(f23,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.75/0.98    inference(rectify,[],[f22])).
% 3.75/0.98  
% 3.75/0.98  fof(f24,plain,(
% 3.75/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f25,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.75/0.98  
% 3.75/0.98  fof(f38,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.75/0.98    inference(cnf_transformation,[],[f25])).
% 3.75/0.98  
% 3.75/0.98  fof(f84,plain,(
% 3.75/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.75/0.98    inference(equality_resolution,[],[f38])).
% 3.75/0.98  
% 3.75/0.98  fof(f37,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.75/0.98    inference(cnf_transformation,[],[f25])).
% 3.75/0.98  
% 3.75/0.98  fof(f85,plain,(
% 3.75/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.75/0.98    inference(equality_resolution,[],[f37])).
% 3.75/0.98  
% 3.75/0.98  fof(f52,plain,(
% 3.75/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.75/0.98    inference(cnf_transformation,[],[f33])).
% 3.75/0.98  
% 3.75/0.98  fof(f80,plain,(
% 3.75/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.75/0.98    inference(definition_unfolding,[],[f52,f67])).
% 3.75/0.98  
% 3.75/0.98  fof(f93,plain,(
% 3.75/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.75/0.98    inference(equality_resolution,[],[f80])).
% 3.75/0.98  
% 3.75/0.98  fof(f94,plain,(
% 3.75/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.75/0.98    inference(equality_resolution,[],[f93])).
% 3.75/0.98  
% 3.75/0.98  fof(f66,plain,(
% 3.75/0.98    ~r2_hidden(sK2,sK3)),
% 3.75/0.98    inference(cnf_transformation,[],[f35])).
% 3.75/0.98  
% 3.75/0.98  cnf(c_14,plain,
% 3.75/0.98      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_25,negated_conjecture,
% 3.75/0.98      ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
% 3.75/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8133,plain,
% 3.75/0.98      ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),sK3) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8279,plain,
% 3.75/0.98      ( r1_tarski(k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 3.75/0.98      inference(demodulation,[status(thm)],[c_14,c_8133]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7,plain,
% 3.75/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.75/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8144,plain,
% 3.75/0.98      ( X0 = X1
% 3.75/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.75/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8509,plain,
% 3.75/0.98      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3
% 3.75/0.98      | r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_8279,c_8144]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_11,plain,
% 3.75/0.98      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 3.75/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8142,plain,
% 3.75/0.98      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10962,plain,
% 3.75/0.98      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 3.75/0.98      inference(forward_subsumption_resolution,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_8509,c_8142]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_19,plain,
% 3.75/0.98      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8139,plain,
% 3.75/0.98      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10,plain,
% 3.75/0.98      ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.75/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,X1)
% 3.75/0.98      | r2_hidden(X0,X2)
% 3.75/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8148,plain,
% 3.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.75/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_9041,plain,
% 3.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = iProver_top
% 3.75/0.98      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_10,c_8148]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4,negated_conjecture,
% 3.75/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8147,plain,
% 3.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_9238,plain,
% 3.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.75/0.98      | r2_hidden(X0,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_9041,c_8147]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_9509,plain,
% 3.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_8139,c_9238]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10977,plain,
% 3.75/0.98      ( r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.75/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_10962,c_9509]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_11032,plain,
% 3.75/0.98      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.75/0.98      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_10977]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_21,plain,
% 3.75/0.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_37,plain,
% 3.75/0.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_39,plain,
% 3.75/0.98      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_37]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_24,negated_conjecture,
% 3.75/0.98      ( ~ r2_hidden(sK2,sK3) ),
% 3.75/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_27,plain,
% 3.75/0.98      ( r2_hidden(sK2,sK3) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(contradiction,plain,
% 3.75/0.98      ( $false ),
% 3.75/0.98      inference(minisat,[status(thm)],[c_11032,c_39,c_27]) ).
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  ------                               Statistics
% 3.75/0.98  
% 3.75/0.98  ------ Selected
% 3.75/0.98  
% 3.75/0.98  total_time:                             0.267
% 3.75/0.98  
%------------------------------------------------------------------------------
