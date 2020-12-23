%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:50 EST 2020

% Result     : Theorem 35.20s
% Output     : CNFRefutation 35.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 131 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  289 ( 337 expanded)
%              Number of equality atoms :  151 ( 187 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f33])).

fof(f65,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f89,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f65,f48,f72])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

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

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f19])).

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

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f99,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f100,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f99])).

fof(f66,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_342,negated_conjecture,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) ),
    inference(theory_normalisation,[status(thm)],[c_23,c_12,c_1])).

cnf(c_133740,plain,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_133828,plain,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_133740])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_133749,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_136658,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3
    | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_133828,c_133749])).

cnf(c_11,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_344,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_12,c_1])).

cnf(c_133739,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_137208,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_136658,c_133739])).

cnf(c_133815,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_12,c_1])).

cnf(c_133736,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_133881,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_133815,c_133736])).

cnf(c_143470,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_137208,c_133881])).

cnf(c_143501,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_143470])).

cnf(c_19,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_30,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143501,c_32,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.20/5.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.20/5.02  
% 35.20/5.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.20/5.02  
% 35.20/5.02  ------  iProver source info
% 35.20/5.02  
% 35.20/5.02  git: date: 2020-06-30 10:37:57 +0100
% 35.20/5.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.20/5.02  git: non_committed_changes: false
% 35.20/5.02  git: last_make_outside_of_git: false
% 35.20/5.02  
% 35.20/5.02  ------ 
% 35.20/5.02  ------ Parsing...
% 35.20/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  ------ Proving...
% 35.20/5.02  ------ Problem Properties 
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  clauses                                 23
% 35.20/5.02  conjectures                             2
% 35.20/5.02  EPR                                     3
% 35.20/5.02  Horn                                    19
% 35.20/5.02  unary                                   11
% 35.20/5.02  binary                                  2
% 35.20/5.02  lits                                    49
% 35.20/5.02  lits eq                                 21
% 35.20/5.02  fd_pure                                 0
% 35.20/5.02  fd_pseudo                               0
% 35.20/5.02  fd_cond                                 0
% 35.20/5.02  fd_pseudo_cond                          8
% 35.20/5.02  AC symbols                              1
% 35.20/5.02  
% 35.20/5.02  ------ Input Options Time Limit: Unbounded
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing...
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.20/5.02  Current options:
% 35.20/5.02  ------ 
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing...
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/5.02  
% 35.20/5.02  ------ Proving...
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  % SZS status Theorem for theBenchmark.p
% 35.20/5.02  
% 35.20/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 35.20/5.02  
% 35.20/5.02  fof(f1,axiom,(
% 35.20/5.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f35,plain,(
% 35.20/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f1])).
% 35.20/5.02  
% 35.20/5.02  fof(f17,conjecture,(
% 35.20/5.02    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f18,negated_conjecture,(
% 35.20/5.02    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 35.20/5.02    inference(negated_conjecture,[],[f17])).
% 35.20/5.02  
% 35.20/5.02  fof(f20,plain,(
% 35.20/5.02    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 35.20/5.02    inference(ennf_transformation,[],[f18])).
% 35.20/5.02  
% 35.20/5.02  fof(f33,plain,(
% 35.20/5.02    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 35.20/5.02    introduced(choice_axiom,[])).
% 35.20/5.02  
% 35.20/5.02  fof(f34,plain,(
% 35.20/5.02    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 35.20/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f33])).
% 35.20/5.02  
% 35.20/5.02  fof(f65,plain,(
% 35.20/5.02    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 35.20/5.02    inference(cnf_transformation,[],[f34])).
% 35.20/5.02  
% 35.20/5.02  fof(f7,axiom,(
% 35.20/5.02    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f48,plain,(
% 35.20/5.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f7])).
% 35.20/5.02  
% 35.20/5.02  fof(f9,axiom,(
% 35.20/5.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f57,plain,(
% 35.20/5.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f9])).
% 35.20/5.02  
% 35.20/5.02  fof(f10,axiom,(
% 35.20/5.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f58,plain,(
% 35.20/5.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f10])).
% 35.20/5.02  
% 35.20/5.02  fof(f11,axiom,(
% 35.20/5.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f59,plain,(
% 35.20/5.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f11])).
% 35.20/5.02  
% 35.20/5.02  fof(f12,axiom,(
% 35.20/5.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f60,plain,(
% 35.20/5.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f12])).
% 35.20/5.02  
% 35.20/5.02  fof(f13,axiom,(
% 35.20/5.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f61,plain,(
% 35.20/5.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f13])).
% 35.20/5.02  
% 35.20/5.02  fof(f14,axiom,(
% 35.20/5.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f62,plain,(
% 35.20/5.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f14])).
% 35.20/5.02  
% 35.20/5.02  fof(f15,axiom,(
% 35.20/5.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f63,plain,(
% 35.20/5.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f15])).
% 35.20/5.02  
% 35.20/5.02  fof(f67,plain,(
% 35.20/5.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 35.20/5.02    inference(definition_unfolding,[],[f62,f63])).
% 35.20/5.02  
% 35.20/5.02  fof(f68,plain,(
% 35.20/5.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 35.20/5.02    inference(definition_unfolding,[],[f61,f67])).
% 35.20/5.02  
% 35.20/5.02  fof(f69,plain,(
% 35.20/5.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 35.20/5.02    inference(definition_unfolding,[],[f60,f68])).
% 35.20/5.02  
% 35.20/5.02  fof(f70,plain,(
% 35.20/5.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 35.20/5.02    inference(definition_unfolding,[],[f59,f69])).
% 35.20/5.02  
% 35.20/5.02  fof(f71,plain,(
% 35.20/5.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 35.20/5.02    inference(definition_unfolding,[],[f58,f70])).
% 35.20/5.02  
% 35.20/5.02  fof(f72,plain,(
% 35.20/5.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 35.20/5.02    inference(definition_unfolding,[],[f57,f71])).
% 35.20/5.02  
% 35.20/5.02  fof(f89,plain,(
% 35.20/5.02    r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3)),
% 35.20/5.02    inference(definition_unfolding,[],[f65,f48,f72])).
% 35.20/5.02  
% 35.20/5.02  fof(f6,axiom,(
% 35.20/5.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f47,plain,(
% 35.20/5.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f6])).
% 35.20/5.02  
% 35.20/5.02  fof(f2,axiom,(
% 35.20/5.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f36,plain,(
% 35.20/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f2])).
% 35.20/5.02  
% 35.20/5.02  fof(f4,axiom,(
% 35.20/5.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f26,plain,(
% 35.20/5.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.20/5.02    inference(nnf_transformation,[],[f4])).
% 35.20/5.02  
% 35.20/5.02  fof(f27,plain,(
% 35.20/5.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.20/5.02    inference(flattening,[],[f26])).
% 35.20/5.02  
% 35.20/5.02  fof(f45,plain,(
% 35.20/5.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.20/5.02    inference(cnf_transformation,[],[f27])).
% 35.20/5.02  
% 35.20/5.02  fof(f5,axiom,(
% 35.20/5.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f46,plain,(
% 35.20/5.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.20/5.02    inference(cnf_transformation,[],[f5])).
% 35.20/5.02  
% 35.20/5.02  fof(f79,plain,(
% 35.20/5.02    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 35.20/5.02    inference(definition_unfolding,[],[f46,f48])).
% 35.20/5.02  
% 35.20/5.02  fof(f3,axiom,(
% 35.20/5.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f21,plain,(
% 35.20/5.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.20/5.02    inference(nnf_transformation,[],[f3])).
% 35.20/5.02  
% 35.20/5.02  fof(f22,plain,(
% 35.20/5.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.20/5.02    inference(flattening,[],[f21])).
% 35.20/5.02  
% 35.20/5.02  fof(f23,plain,(
% 35.20/5.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.20/5.02    inference(rectify,[],[f22])).
% 35.20/5.02  
% 35.20/5.02  fof(f24,plain,(
% 35.20/5.02    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.20/5.02    introduced(choice_axiom,[])).
% 35.20/5.02  
% 35.20/5.02  fof(f25,plain,(
% 35.20/5.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.20/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 35.20/5.02  
% 35.20/5.02  fof(f39,plain,(
% 35.20/5.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 35.20/5.02    inference(cnf_transformation,[],[f25])).
% 35.20/5.02  
% 35.20/5.02  fof(f76,plain,(
% 35.20/5.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != X2) )),
% 35.20/5.02    inference(definition_unfolding,[],[f39,f48])).
% 35.20/5.02  
% 35.20/5.02  fof(f90,plain,(
% 35.20/5.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 35.20/5.02    inference(equality_resolution,[],[f76])).
% 35.20/5.02  
% 35.20/5.02  fof(f8,axiom,(
% 35.20/5.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 35.20/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.20/5.02  
% 35.20/5.02  fof(f19,plain,(
% 35.20/5.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 35.20/5.02    inference(ennf_transformation,[],[f8])).
% 35.20/5.02  
% 35.20/5.02  fof(f28,plain,(
% 35.20/5.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.20/5.02    inference(nnf_transformation,[],[f19])).
% 35.20/5.02  
% 35.20/5.02  fof(f29,plain,(
% 35.20/5.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.20/5.02    inference(flattening,[],[f28])).
% 35.20/5.02  
% 35.20/5.02  fof(f30,plain,(
% 35.20/5.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.20/5.02    inference(rectify,[],[f29])).
% 35.20/5.02  
% 35.20/5.02  fof(f31,plain,(
% 35.20/5.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 35.20/5.02    introduced(choice_axiom,[])).
% 35.20/5.02  
% 35.20/5.02  fof(f32,plain,(
% 35.20/5.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.20/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 35.20/5.02  
% 35.20/5.02  fof(f50,plain,(
% 35.20/5.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 35.20/5.02    inference(cnf_transformation,[],[f32])).
% 35.20/5.02  
% 35.20/5.02  fof(f86,plain,(
% 35.20/5.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 35.20/5.02    inference(definition_unfolding,[],[f50,f70])).
% 35.20/5.02  
% 35.20/5.02  fof(f99,plain,(
% 35.20/5.02    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 35.20/5.02    inference(equality_resolution,[],[f86])).
% 35.20/5.02  
% 35.20/5.02  fof(f100,plain,(
% 35.20/5.02    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 35.20/5.02    inference(equality_resolution,[],[f99])).
% 35.20/5.02  
% 35.20/5.02  fof(f66,plain,(
% 35.20/5.02    ~r2_hidden(sK2,sK3)),
% 35.20/5.02    inference(cnf_transformation,[],[f34])).
% 35.20/5.02  
% 35.20/5.02  cnf(c_0,plain,
% 35.20/5.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.20/5.02      inference(cnf_transformation,[],[f35]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_23,negated_conjecture,
% 35.20/5.02      ( r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
% 35.20/5.02      inference(cnf_transformation,[],[f89]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_12,plain,
% 35.20/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.20/5.02      inference(cnf_transformation,[],[f47]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_1,plain,
% 35.20/5.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 35.20/5.02      inference(cnf_transformation,[],[f36]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_342,negated_conjecture,
% 35.20/5.02      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) ),
% 35.20/5.02      inference(theory_normalisation,[status(thm)],[c_23,c_12,c_1]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133740,plain,
% 35.20/5.02      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) = iProver_top ),
% 35.20/5.02      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133828,plain,
% 35.20/5.02      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),sK3) = iProver_top ),
% 35.20/5.02      inference(demodulation,[status(thm)],[c_0,c_133740]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_8,plain,
% 35.20/5.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.20/5.02      inference(cnf_transformation,[],[f45]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133749,plain,
% 35.20/5.02      ( X0 = X1
% 35.20/5.02      | r1_tarski(X0,X1) != iProver_top
% 35.20/5.02      | r1_tarski(X1,X0) != iProver_top ),
% 35.20/5.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_136658,plain,
% 35.20/5.02      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3
% 35.20/5.02      | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) != iProver_top ),
% 35.20/5.02      inference(superposition,[status(thm)],[c_133828,c_133749]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_11,plain,
% 35.20/5.02      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
% 35.20/5.02      inference(cnf_transformation,[],[f79]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_344,plain,
% 35.20/5.02      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
% 35.20/5.02      inference(theory_normalisation,[status(thm)],[c_11,c_12,c_1]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133739,plain,
% 35.20/5.02      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
% 35.20/5.02      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_137208,plain,
% 35.20/5.02      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
% 35.20/5.02      inference(forward_subsumption_resolution,
% 35.20/5.02                [status(thm)],
% 35.20/5.02                [c_136658,c_133739]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133815,plain,
% 35.20/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 35.20/5.02      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_5,plain,
% 35.20/5.02      ( ~ r2_hidden(X0,X1)
% 35.20/5.02      | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) ),
% 35.20/5.02      inference(cnf_transformation,[],[f90]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_347,plain,
% 35.20/5.02      ( ~ r2_hidden(X0,X1)
% 35.20/5.02      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 35.20/5.02      inference(theory_normalisation,[status(thm)],[c_5,c_12,c_1]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133736,plain,
% 35.20/5.02      ( r2_hidden(X0,X1) != iProver_top
% 35.20/5.02      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top ),
% 35.20/5.02      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_133881,plain,
% 35.20/5.02      ( r2_hidden(X0,X1) != iProver_top
% 35.20/5.02      | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = iProver_top ),
% 35.20/5.02      inference(superposition,[status(thm)],[c_133815,c_133736]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_143470,plain,
% 35.20/5.02      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 35.20/5.02      | r2_hidden(X0,sK3) = iProver_top ),
% 35.20/5.02      inference(superposition,[status(thm)],[c_137208,c_133881]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_143501,plain,
% 35.20/5.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 35.20/5.02      | r2_hidden(sK2,sK3) = iProver_top ),
% 35.20/5.02      inference(instantiation,[status(thm)],[c_143470]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_19,plain,
% 35.20/5.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 35.20/5.02      inference(cnf_transformation,[],[f100]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_30,plain,
% 35.20/5.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 35.20/5.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_32,plain,
% 35.20/5.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 35.20/5.02      inference(instantiation,[status(thm)],[c_30]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_22,negated_conjecture,
% 35.20/5.02      ( ~ r2_hidden(sK2,sK3) ),
% 35.20/5.02      inference(cnf_transformation,[],[f66]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(c_25,plain,
% 35.20/5.02      ( r2_hidden(sK2,sK3) != iProver_top ),
% 35.20/5.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.20/5.02  
% 35.20/5.02  cnf(contradiction,plain,
% 35.20/5.02      ( $false ),
% 35.20/5.02      inference(minisat,[status(thm)],[c_143501,c_32,c_25]) ).
% 35.20/5.02  
% 35.20/5.02  
% 35.20/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 35.20/5.02  
% 35.20/5.02  ------                               Statistics
% 35.20/5.02  
% 35.20/5.02  ------ Selected
% 35.20/5.02  
% 35.20/5.02  total_time:                             4.111
% 35.20/5.02  
%------------------------------------------------------------------------------
