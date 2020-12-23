%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:35 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  155 (1944 expanded)
%              Number of clauses        :   80 ( 334 expanded)
%              Number of leaves         :   19 ( 544 expanded)
%              Depth                    :   21
%              Number of atoms          :  440 (5209 expanded)
%              Number of equality atoms :  252 (3121 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f26])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & sK5 != sK6
      & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & sK5 != sK6
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f34])).

fof(f59,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f78,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f59,f65,f66])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f86,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f84,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f76])).

fof(f85,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f84])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f62,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_610,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_617,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1850,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_617])).

cnf(c_15,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_605,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_613,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1717,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_613])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_603,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1830,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_603])).

cnf(c_2250,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK6
    | sK3(X0,sK6) = X0
    | sK3(X0,sK6) = sK4 ),
    inference(superposition,[status(thm)],[c_605,c_1830])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_612,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1279,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_612])).

cnf(c_10447,plain,
    ( sK3(sK4,sK6) = sK4
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_1279])).

cnf(c_11193,plain,
    ( sK3(sK4,sK6) = sK4
    | k1_xboole_0 = X0
    | r2_hidden(sK2(X0),sK6) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_10447])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_927,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_930,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_618,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_619,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1829,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_619])).

cnf(c_2350,plain,
    ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_1829])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_609,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2490,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2350,c_609])).

cnf(c_20,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_316,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_756,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_879,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_315,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_880,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_854,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_926,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_13,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_607,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_898,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_607])).

cnf(c_1234,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_609])).

cnf(c_1297,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_603])).

cnf(c_1384,plain,
    ( sK2(sK5) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_610,c_1297])).

cnf(c_1509,plain,
    ( sK2(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1384,c_19,c_879,c_880])).

cnf(c_1512,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_610])).

cnf(c_859,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_960,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_4736,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | sK6 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_1143,plain,
    ( X0 != X1
    | X0 = k3_enumset1(X2,X2,X2,X2,X2)
    | k3_enumset1(X2,X2,X2,X2,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_4738,plain,
    ( X0 != X1
    | X0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_4739,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
    | sK5 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4738])).

cnf(c_1152,plain,
    ( sK0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X0
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_603])).

cnf(c_6378,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | sK0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_1152,c_1234])).

cnf(c_8259,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6378,c_619])).

cnf(c_757,plain,
    ( sK5 != X0
    | sK5 = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_12175,plain,
    ( sK5 != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK5 = sK6
    | sK6 != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_17203,plain,
    ( r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2490,c_20,c_19,c_23,c_26,c_879,c_880,c_926,c_927,c_1234,c_1512,c_4736,c_4739,c_8259,c_12175])).

cnf(c_17210,plain,
    ( sK3(sK4,sK6) = sK4
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_17203])).

cnf(c_27620,plain,
    ( sK3(sK4,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11193,c_930,c_17210])).

cnf(c_14,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_606,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) != X0
    | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_27624,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | r2_hidden(sK3(sK4,sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_27620,c_606])).

cnf(c_27629,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27624,c_27620])).

cnf(c_1699,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
    | sK3(X0,sK5) = X0
    | sK3(X0,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_605,c_1297])).

cnf(c_8357,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | sK3(sK4,sK5) = sK4
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1234])).

cnf(c_21213,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8357,c_19,c_879,c_880,c_1234,c_1512,c_8259])).

cnf(c_27630,plain,
    ( sK5 = sK6
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27629,c_21213])).

cnf(c_755,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_6438,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_2249,plain,
    ( sK2(sK6) = sK4
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_610,c_1830])).

cnf(c_2638,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_610])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27630,c_6438,c_2638,c_880,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.66/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/1.50  
% 6.66/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.66/1.50  
% 6.66/1.50  ------  iProver source info
% 6.66/1.50  
% 6.66/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.66/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.66/1.50  git: non_committed_changes: false
% 6.66/1.50  git: last_make_outside_of_git: false
% 6.66/1.50  
% 6.66/1.50  ------ 
% 6.66/1.50  
% 6.66/1.50  ------ Input Options
% 6.66/1.50  
% 6.66/1.50  --out_options                           all
% 6.66/1.50  --tptp_safe_out                         true
% 6.66/1.50  --problem_path                          ""
% 6.66/1.50  --include_path                          ""
% 6.66/1.50  --clausifier                            res/vclausify_rel
% 6.66/1.50  --clausifier_options                    --mode clausify
% 6.66/1.50  --stdin                                 false
% 6.66/1.50  --stats_out                             all
% 6.66/1.50  
% 6.66/1.50  ------ General Options
% 6.66/1.50  
% 6.66/1.50  --fof                                   false
% 6.66/1.50  --time_out_real                         305.
% 6.66/1.50  --time_out_virtual                      -1.
% 6.66/1.50  --symbol_type_check                     false
% 6.66/1.50  --clausify_out                          false
% 6.66/1.50  --sig_cnt_out                           false
% 6.66/1.50  --trig_cnt_out                          false
% 6.66/1.50  --trig_cnt_out_tolerance                1.
% 6.66/1.50  --trig_cnt_out_sk_spl                   false
% 6.66/1.50  --abstr_cl_out                          false
% 6.66/1.50  
% 6.66/1.50  ------ Global Options
% 6.66/1.50  
% 6.66/1.50  --schedule                              default
% 6.66/1.50  --add_important_lit                     false
% 6.66/1.50  --prop_solver_per_cl                    1000
% 6.66/1.50  --min_unsat_core                        false
% 6.66/1.50  --soft_assumptions                      false
% 6.66/1.50  --soft_lemma_size                       3
% 6.66/1.50  --prop_impl_unit_size                   0
% 6.66/1.50  --prop_impl_unit                        []
% 6.66/1.50  --share_sel_clauses                     true
% 6.66/1.50  --reset_solvers                         false
% 6.66/1.50  --bc_imp_inh                            [conj_cone]
% 6.66/1.50  --conj_cone_tolerance                   3.
% 6.66/1.50  --extra_neg_conj                        none
% 6.66/1.50  --large_theory_mode                     true
% 6.66/1.50  --prolific_symb_bound                   200
% 6.66/1.50  --lt_threshold                          2000
% 6.66/1.50  --clause_weak_htbl                      true
% 6.66/1.50  --gc_record_bc_elim                     false
% 6.66/1.50  
% 6.66/1.50  ------ Preprocessing Options
% 6.66/1.50  
% 6.66/1.50  --preprocessing_flag                    true
% 6.66/1.50  --time_out_prep_mult                    0.1
% 6.66/1.50  --splitting_mode                        input
% 6.66/1.50  --splitting_grd                         true
% 6.66/1.50  --splitting_cvd                         false
% 6.66/1.50  --splitting_cvd_svl                     false
% 6.66/1.50  --splitting_nvd                         32
% 6.66/1.50  --sub_typing                            true
% 6.66/1.50  --prep_gs_sim                           true
% 6.66/1.50  --prep_unflatten                        true
% 6.66/1.50  --prep_res_sim                          true
% 6.66/1.50  --prep_upred                            true
% 6.66/1.50  --prep_sem_filter                       exhaustive
% 6.66/1.50  --prep_sem_filter_out                   false
% 6.66/1.50  --pred_elim                             true
% 6.66/1.50  --res_sim_input                         true
% 6.66/1.50  --eq_ax_congr_red                       true
% 6.66/1.50  --pure_diseq_elim                       true
% 6.66/1.50  --brand_transform                       false
% 6.66/1.50  --non_eq_to_eq                          false
% 6.66/1.50  --prep_def_merge                        true
% 6.66/1.50  --prep_def_merge_prop_impl              false
% 6.66/1.50  --prep_def_merge_mbd                    true
% 6.66/1.50  --prep_def_merge_tr_red                 false
% 6.66/1.50  --prep_def_merge_tr_cl                  false
% 6.66/1.50  --smt_preprocessing                     true
% 6.66/1.50  --smt_ac_axioms                         fast
% 6.66/1.50  --preprocessed_out                      false
% 6.66/1.50  --preprocessed_stats                    false
% 6.66/1.50  
% 6.66/1.50  ------ Abstraction refinement Options
% 6.66/1.50  
% 6.66/1.50  --abstr_ref                             []
% 6.66/1.50  --abstr_ref_prep                        false
% 6.66/1.50  --abstr_ref_until_sat                   false
% 6.66/1.50  --abstr_ref_sig_restrict                funpre
% 6.66/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.66/1.50  --abstr_ref_under                       []
% 6.66/1.50  
% 6.66/1.50  ------ SAT Options
% 6.66/1.50  
% 6.66/1.50  --sat_mode                              false
% 6.66/1.50  --sat_fm_restart_options                ""
% 6.66/1.50  --sat_gr_def                            false
% 6.66/1.50  --sat_epr_types                         true
% 6.66/1.50  --sat_non_cyclic_types                  false
% 6.66/1.50  --sat_finite_models                     false
% 6.66/1.50  --sat_fm_lemmas                         false
% 6.66/1.50  --sat_fm_prep                           false
% 6.66/1.50  --sat_fm_uc_incr                        true
% 6.66/1.50  --sat_out_model                         small
% 6.66/1.50  --sat_out_clauses                       false
% 6.66/1.50  
% 6.66/1.50  ------ QBF Options
% 6.66/1.50  
% 6.66/1.50  --qbf_mode                              false
% 6.66/1.50  --qbf_elim_univ                         false
% 6.66/1.50  --qbf_dom_inst                          none
% 6.66/1.50  --qbf_dom_pre_inst                      false
% 6.66/1.50  --qbf_sk_in                             false
% 6.66/1.50  --qbf_pred_elim                         true
% 6.66/1.50  --qbf_split                             512
% 6.66/1.50  
% 6.66/1.50  ------ BMC1 Options
% 6.66/1.50  
% 6.66/1.50  --bmc1_incremental                      false
% 6.66/1.50  --bmc1_axioms                           reachable_all
% 6.66/1.50  --bmc1_min_bound                        0
% 6.66/1.50  --bmc1_max_bound                        -1
% 6.66/1.50  --bmc1_max_bound_default                -1
% 6.66/1.50  --bmc1_symbol_reachability              true
% 6.66/1.50  --bmc1_property_lemmas                  false
% 6.66/1.50  --bmc1_k_induction                      false
% 6.66/1.50  --bmc1_non_equiv_states                 false
% 6.66/1.50  --bmc1_deadlock                         false
% 6.66/1.50  --bmc1_ucm                              false
% 6.66/1.50  --bmc1_add_unsat_core                   none
% 6.66/1.50  --bmc1_unsat_core_children              false
% 6.66/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.66/1.50  --bmc1_out_stat                         full
% 6.66/1.50  --bmc1_ground_init                      false
% 6.66/1.50  --bmc1_pre_inst_next_state              false
% 6.66/1.50  --bmc1_pre_inst_state                   false
% 6.66/1.50  --bmc1_pre_inst_reach_state             false
% 6.66/1.50  --bmc1_out_unsat_core                   false
% 6.66/1.50  --bmc1_aig_witness_out                  false
% 6.66/1.50  --bmc1_verbose                          false
% 6.66/1.50  --bmc1_dump_clauses_tptp                false
% 6.66/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.66/1.50  --bmc1_dump_file                        -
% 6.66/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.66/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.66/1.50  --bmc1_ucm_extend_mode                  1
% 6.66/1.50  --bmc1_ucm_init_mode                    2
% 6.66/1.50  --bmc1_ucm_cone_mode                    none
% 6.66/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.66/1.50  --bmc1_ucm_relax_model                  4
% 6.66/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.66/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.66/1.50  --bmc1_ucm_layered_model                none
% 6.66/1.50  --bmc1_ucm_max_lemma_size               10
% 6.66/1.50  
% 6.66/1.50  ------ AIG Options
% 6.66/1.50  
% 6.66/1.50  --aig_mode                              false
% 6.66/1.50  
% 6.66/1.50  ------ Instantiation Options
% 6.66/1.50  
% 6.66/1.50  --instantiation_flag                    true
% 6.66/1.50  --inst_sos_flag                         false
% 6.66/1.50  --inst_sos_phase                        true
% 6.66/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.66/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.66/1.50  --inst_lit_sel_side                     num_symb
% 6.66/1.50  --inst_solver_per_active                1400
% 6.66/1.50  --inst_solver_calls_frac                1.
% 6.66/1.50  --inst_passive_queue_type               priority_queues
% 6.66/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.66/1.50  --inst_passive_queues_freq              [25;2]
% 6.66/1.50  --inst_dismatching                      true
% 6.66/1.50  --inst_eager_unprocessed_to_passive     true
% 6.66/1.50  --inst_prop_sim_given                   true
% 6.66/1.50  --inst_prop_sim_new                     false
% 6.66/1.50  --inst_subs_new                         false
% 6.66/1.50  --inst_eq_res_simp                      false
% 6.66/1.50  --inst_subs_given                       false
% 6.66/1.50  --inst_orphan_elimination               true
% 6.66/1.50  --inst_learning_loop_flag               true
% 6.66/1.50  --inst_learning_start                   3000
% 6.66/1.50  --inst_learning_factor                  2
% 6.66/1.50  --inst_start_prop_sim_after_learn       3
% 6.66/1.50  --inst_sel_renew                        solver
% 6.66/1.50  --inst_lit_activity_flag                true
% 6.66/1.50  --inst_restr_to_given                   false
% 6.66/1.50  --inst_activity_threshold               500
% 6.66/1.50  --inst_out_proof                        true
% 6.66/1.50  
% 6.66/1.50  ------ Resolution Options
% 6.66/1.50  
% 6.66/1.50  --resolution_flag                       true
% 6.66/1.50  --res_lit_sel                           adaptive
% 6.66/1.50  --res_lit_sel_side                      none
% 6.66/1.50  --res_ordering                          kbo
% 6.66/1.50  --res_to_prop_solver                    active
% 6.66/1.50  --res_prop_simpl_new                    false
% 6.66/1.50  --res_prop_simpl_given                  true
% 6.66/1.50  --res_passive_queue_type                priority_queues
% 6.66/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.66/1.50  --res_passive_queues_freq               [15;5]
% 6.66/1.50  --res_forward_subs                      full
% 6.66/1.50  --res_backward_subs                     full
% 6.66/1.50  --res_forward_subs_resolution           true
% 6.66/1.50  --res_backward_subs_resolution          true
% 6.66/1.50  --res_orphan_elimination                true
% 6.66/1.50  --res_time_limit                        2.
% 6.66/1.50  --res_out_proof                         true
% 6.66/1.50  
% 6.66/1.50  ------ Superposition Options
% 6.66/1.50  
% 6.66/1.50  --superposition_flag                    true
% 6.66/1.50  --sup_passive_queue_type                priority_queues
% 6.66/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.66/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.66/1.50  --demod_completeness_check              fast
% 6.66/1.50  --demod_use_ground                      true
% 6.66/1.50  --sup_to_prop_solver                    passive
% 6.66/1.50  --sup_prop_simpl_new                    true
% 6.66/1.50  --sup_prop_simpl_given                  true
% 6.66/1.50  --sup_fun_splitting                     false
% 6.66/1.50  --sup_smt_interval                      50000
% 6.66/1.50  
% 6.66/1.50  ------ Superposition Simplification Setup
% 6.66/1.50  
% 6.66/1.50  --sup_indices_passive                   []
% 6.66/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.66/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.66/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.66/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.66/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.66/1.50  --sup_full_bw                           [BwDemod]
% 6.66/1.50  --sup_immed_triv                        [TrivRules]
% 6.66/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.66/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.66/1.50  --sup_immed_bw_main                     []
% 6.66/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.66/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.66/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.66/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.66/1.50  
% 6.66/1.50  ------ Combination Options
% 6.66/1.50  
% 6.66/1.50  --comb_res_mult                         3
% 6.66/1.50  --comb_sup_mult                         2
% 6.66/1.50  --comb_inst_mult                        10
% 6.66/1.50  
% 6.66/1.50  ------ Debug Options
% 6.66/1.50  
% 6.66/1.50  --dbg_backtrace                         false
% 6.66/1.50  --dbg_dump_prop_clauses                 false
% 6.66/1.50  --dbg_dump_prop_clauses_file            -
% 6.66/1.50  --dbg_out_stat                          false
% 6.66/1.50  ------ Parsing...
% 6.66/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.66/1.50  
% 6.66/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.66/1.50  
% 6.66/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.66/1.50  
% 6.66/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.66/1.50  ------ Proving...
% 6.66/1.50  ------ Problem Properties 
% 6.66/1.50  
% 6.66/1.50  
% 6.66/1.50  clauses                                 21
% 6.66/1.50  conjectures                             4
% 6.66/1.50  EPR                                     6
% 6.66/1.50  Horn                                    16
% 6.66/1.50  unary                                   7
% 6.66/1.50  binary                                  6
% 6.66/1.50  lits                                    44
% 6.66/1.50  lits eq                                 14
% 6.66/1.50  fd_pure                                 0
% 6.66/1.50  fd_pseudo                               0
% 6.66/1.50  fd_cond                                 1
% 6.66/1.50  fd_pseudo_cond                          6
% 6.66/1.50  AC symbols                              0
% 6.66/1.50  
% 6.66/1.50  ------ Schedule dynamic 5 is on 
% 6.66/1.50  
% 6.66/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.66/1.50  
% 6.66/1.50  
% 6.66/1.50  ------ 
% 6.66/1.50  Current options:
% 6.66/1.50  ------ 
% 6.66/1.50  
% 6.66/1.50  ------ Input Options
% 6.66/1.50  
% 6.66/1.50  --out_options                           all
% 6.66/1.50  --tptp_safe_out                         true
% 6.66/1.50  --problem_path                          ""
% 6.66/1.50  --include_path                          ""
% 6.66/1.50  --clausifier                            res/vclausify_rel
% 6.66/1.50  --clausifier_options                    --mode clausify
% 6.66/1.50  --stdin                                 false
% 6.66/1.50  --stats_out                             all
% 6.66/1.50  
% 6.66/1.50  ------ General Options
% 6.66/1.50  
% 6.66/1.50  --fof                                   false
% 6.66/1.50  --time_out_real                         305.
% 6.66/1.50  --time_out_virtual                      -1.
% 6.66/1.50  --symbol_type_check                     false
% 6.66/1.50  --clausify_out                          false
% 6.66/1.50  --sig_cnt_out                           false
% 6.66/1.50  --trig_cnt_out                          false
% 6.66/1.50  --trig_cnt_out_tolerance                1.
% 6.66/1.50  --trig_cnt_out_sk_spl                   false
% 6.66/1.50  --abstr_cl_out                          false
% 6.66/1.50  
% 6.66/1.50  ------ Global Options
% 6.66/1.50  
% 6.66/1.50  --schedule                              default
% 6.66/1.50  --add_important_lit                     false
% 6.66/1.50  --prop_solver_per_cl                    1000
% 6.66/1.50  --min_unsat_core                        false
% 6.66/1.50  --soft_assumptions                      false
% 6.66/1.50  --soft_lemma_size                       3
% 6.66/1.50  --prop_impl_unit_size                   0
% 6.66/1.50  --prop_impl_unit                        []
% 6.66/1.50  --share_sel_clauses                     true
% 6.66/1.50  --reset_solvers                         false
% 6.66/1.50  --bc_imp_inh                            [conj_cone]
% 6.66/1.50  --conj_cone_tolerance                   3.
% 6.66/1.50  --extra_neg_conj                        none
% 6.66/1.50  --large_theory_mode                     true
% 6.66/1.50  --prolific_symb_bound                   200
% 6.66/1.50  --lt_threshold                          2000
% 6.66/1.50  --clause_weak_htbl                      true
% 6.66/1.50  --gc_record_bc_elim                     false
% 6.66/1.50  
% 6.66/1.50  ------ Preprocessing Options
% 6.66/1.50  
% 6.66/1.50  --preprocessing_flag                    true
% 6.66/1.50  --time_out_prep_mult                    0.1
% 6.66/1.50  --splitting_mode                        input
% 6.66/1.50  --splitting_grd                         true
% 6.66/1.50  --splitting_cvd                         false
% 6.66/1.50  --splitting_cvd_svl                     false
% 6.66/1.50  --splitting_nvd                         32
% 6.66/1.50  --sub_typing                            true
% 6.66/1.50  --prep_gs_sim                           true
% 6.66/1.50  --prep_unflatten                        true
% 6.66/1.50  --prep_res_sim                          true
% 6.66/1.50  --prep_upred                            true
% 6.66/1.50  --prep_sem_filter                       exhaustive
% 6.66/1.50  --prep_sem_filter_out                   false
% 6.66/1.50  --pred_elim                             true
% 6.66/1.50  --res_sim_input                         true
% 6.66/1.50  --eq_ax_congr_red                       true
% 6.66/1.50  --pure_diseq_elim                       true
% 6.66/1.50  --brand_transform                       false
% 6.66/1.50  --non_eq_to_eq                          false
% 6.66/1.50  --prep_def_merge                        true
% 6.66/1.50  --prep_def_merge_prop_impl              false
% 6.66/1.50  --prep_def_merge_mbd                    true
% 6.66/1.50  --prep_def_merge_tr_red                 false
% 6.66/1.50  --prep_def_merge_tr_cl                  false
% 6.66/1.50  --smt_preprocessing                     true
% 6.66/1.50  --smt_ac_axioms                         fast
% 6.66/1.50  --preprocessed_out                      false
% 6.66/1.50  --preprocessed_stats                    false
% 6.66/1.50  
% 6.66/1.50  ------ Abstraction refinement Options
% 6.66/1.50  
% 6.66/1.50  --abstr_ref                             []
% 6.66/1.50  --abstr_ref_prep                        false
% 6.66/1.50  --abstr_ref_until_sat                   false
% 6.66/1.50  --abstr_ref_sig_restrict                funpre
% 6.66/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.66/1.50  --abstr_ref_under                       []
% 6.66/1.50  
% 6.66/1.50  ------ SAT Options
% 6.66/1.50  
% 6.66/1.50  --sat_mode                              false
% 6.66/1.50  --sat_fm_restart_options                ""
% 6.66/1.50  --sat_gr_def                            false
% 6.66/1.50  --sat_epr_types                         true
% 6.66/1.50  --sat_non_cyclic_types                  false
% 6.66/1.50  --sat_finite_models                     false
% 6.66/1.50  --sat_fm_lemmas                         false
% 6.66/1.50  --sat_fm_prep                           false
% 6.66/1.50  --sat_fm_uc_incr                        true
% 6.66/1.50  --sat_out_model                         small
% 6.66/1.50  --sat_out_clauses                       false
% 6.66/1.50  
% 6.66/1.50  ------ QBF Options
% 6.66/1.50  
% 6.66/1.50  --qbf_mode                              false
% 6.66/1.50  --qbf_elim_univ                         false
% 6.66/1.50  --qbf_dom_inst                          none
% 6.66/1.50  --qbf_dom_pre_inst                      false
% 6.66/1.50  --qbf_sk_in                             false
% 6.66/1.50  --qbf_pred_elim                         true
% 6.66/1.50  --qbf_split                             512
% 6.66/1.50  
% 6.66/1.50  ------ BMC1 Options
% 6.66/1.50  
% 6.66/1.50  --bmc1_incremental                      false
% 6.66/1.50  --bmc1_axioms                           reachable_all
% 6.66/1.50  --bmc1_min_bound                        0
% 6.66/1.50  --bmc1_max_bound                        -1
% 6.66/1.50  --bmc1_max_bound_default                -1
% 6.66/1.50  --bmc1_symbol_reachability              true
% 6.66/1.50  --bmc1_property_lemmas                  false
% 6.66/1.50  --bmc1_k_induction                      false
% 6.66/1.50  --bmc1_non_equiv_states                 false
% 6.66/1.50  --bmc1_deadlock                         false
% 6.66/1.50  --bmc1_ucm                              false
% 6.66/1.50  --bmc1_add_unsat_core                   none
% 6.66/1.50  --bmc1_unsat_core_children              false
% 6.66/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.66/1.50  --bmc1_out_stat                         full
% 6.66/1.50  --bmc1_ground_init                      false
% 6.66/1.50  --bmc1_pre_inst_next_state              false
% 6.66/1.50  --bmc1_pre_inst_state                   false
% 6.66/1.50  --bmc1_pre_inst_reach_state             false
% 6.66/1.50  --bmc1_out_unsat_core                   false
% 6.66/1.50  --bmc1_aig_witness_out                  false
% 6.66/1.50  --bmc1_verbose                          false
% 6.66/1.50  --bmc1_dump_clauses_tptp                false
% 6.66/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.66/1.50  --bmc1_dump_file                        -
% 6.66/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.66/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.66/1.50  --bmc1_ucm_extend_mode                  1
% 6.66/1.50  --bmc1_ucm_init_mode                    2
% 6.66/1.50  --bmc1_ucm_cone_mode                    none
% 6.66/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.66/1.50  --bmc1_ucm_relax_model                  4
% 6.66/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.66/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.66/1.50  --bmc1_ucm_layered_model                none
% 6.66/1.50  --bmc1_ucm_max_lemma_size               10
% 6.66/1.50  
% 6.66/1.50  ------ AIG Options
% 6.66/1.50  
% 6.66/1.50  --aig_mode                              false
% 6.66/1.50  
% 6.66/1.50  ------ Instantiation Options
% 6.66/1.50  
% 6.66/1.50  --instantiation_flag                    true
% 6.66/1.50  --inst_sos_flag                         false
% 6.66/1.50  --inst_sos_phase                        true
% 6.66/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.66/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.66/1.50  --inst_lit_sel_side                     none
% 6.66/1.50  --inst_solver_per_active                1400
% 6.66/1.50  --inst_solver_calls_frac                1.
% 6.66/1.50  --inst_passive_queue_type               priority_queues
% 6.66/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.66/1.50  --inst_passive_queues_freq              [25;2]
% 6.66/1.50  --inst_dismatching                      true
% 6.66/1.50  --inst_eager_unprocessed_to_passive     true
% 6.66/1.50  --inst_prop_sim_given                   true
% 6.66/1.50  --inst_prop_sim_new                     false
% 6.66/1.50  --inst_subs_new                         false
% 6.66/1.50  --inst_eq_res_simp                      false
% 6.66/1.50  --inst_subs_given                       false
% 6.66/1.50  --inst_orphan_elimination               true
% 6.66/1.50  --inst_learning_loop_flag               true
% 6.66/1.50  --inst_learning_start                   3000
% 6.66/1.50  --inst_learning_factor                  2
% 6.66/1.50  --inst_start_prop_sim_after_learn       3
% 6.66/1.50  --inst_sel_renew                        solver
% 6.66/1.50  --inst_lit_activity_flag                true
% 6.66/1.50  --inst_restr_to_given                   false
% 6.66/1.50  --inst_activity_threshold               500
% 6.66/1.50  --inst_out_proof                        true
% 6.66/1.50  
% 6.66/1.50  ------ Resolution Options
% 6.66/1.50  
% 6.66/1.50  --resolution_flag                       false
% 6.66/1.50  --res_lit_sel                           adaptive
% 6.66/1.50  --res_lit_sel_side                      none
% 6.66/1.50  --res_ordering                          kbo
% 6.66/1.50  --res_to_prop_solver                    active
% 6.66/1.50  --res_prop_simpl_new                    false
% 6.66/1.50  --res_prop_simpl_given                  true
% 6.66/1.50  --res_passive_queue_type                priority_queues
% 6.66/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.66/1.50  --res_passive_queues_freq               [15;5]
% 6.66/1.50  --res_forward_subs                      full
% 6.66/1.50  --res_backward_subs                     full
% 6.66/1.50  --res_forward_subs_resolution           true
% 6.66/1.50  --res_backward_subs_resolution          true
% 6.66/1.50  --res_orphan_elimination                true
% 6.66/1.50  --res_time_limit                        2.
% 6.66/1.50  --res_out_proof                         true
% 6.66/1.50  
% 6.66/1.50  ------ Superposition Options
% 6.66/1.50  
% 6.66/1.50  --superposition_flag                    true
% 6.66/1.50  --sup_passive_queue_type                priority_queues
% 6.66/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.66/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.66/1.50  --demod_completeness_check              fast
% 6.66/1.50  --demod_use_ground                      true
% 6.66/1.50  --sup_to_prop_solver                    passive
% 6.66/1.50  --sup_prop_simpl_new                    true
% 6.66/1.50  --sup_prop_simpl_given                  true
% 6.66/1.50  --sup_fun_splitting                     false
% 6.66/1.50  --sup_smt_interval                      50000
% 6.66/1.50  
% 6.66/1.50  ------ Superposition Simplification Setup
% 6.66/1.50  
% 6.66/1.50  --sup_indices_passive                   []
% 6.66/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.66/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.66/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.66/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.66/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.66/1.50  --sup_full_bw                           [BwDemod]
% 6.66/1.50  --sup_immed_triv                        [TrivRules]
% 6.66/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.66/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.66/1.50  --sup_immed_bw_main                     []
% 6.66/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.66/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.66/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.66/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.66/1.50  
% 6.66/1.50  ------ Combination Options
% 6.66/1.50  
% 6.66/1.50  --comb_res_mult                         3
% 6.66/1.50  --comb_sup_mult                         2
% 6.66/1.50  --comb_inst_mult                        10
% 6.66/1.50  
% 6.66/1.50  ------ Debug Options
% 6.66/1.50  
% 6.66/1.50  --dbg_backtrace                         false
% 6.66/1.50  --dbg_dump_prop_clauses                 false
% 6.66/1.50  --dbg_dump_prop_clauses_file            -
% 6.66/1.50  --dbg_out_stat                          false
% 6.66/1.50  
% 6.66/1.50  
% 6.66/1.50  
% 6.66/1.50  
% 6.66/1.50  ------ Proving...
% 6.66/1.50  
% 6.66/1.50  
% 6.66/1.50  % SZS status Theorem for theBenchmark.p
% 6.66/1.50  
% 6.66/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.66/1.50  
% 6.66/1.50  fof(f3,axiom,(
% 6.66/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f15,plain,(
% 6.66/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 6.66/1.50    inference(ennf_transformation,[],[f3])).
% 6.66/1.50  
% 6.66/1.50  fof(f26,plain,(
% 6.66/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 6.66/1.50    introduced(choice_axiom,[])).
% 6.66/1.50  
% 6.66/1.50  fof(f27,plain,(
% 6.66/1.50    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 6.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f26])).
% 6.66/1.50  
% 6.66/1.50  fof(f45,plain,(
% 6.66/1.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 6.66/1.50    inference(cnf_transformation,[],[f27])).
% 6.66/1.50  
% 6.66/1.50  fof(f1,axiom,(
% 6.66/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f14,plain,(
% 6.66/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.66/1.50    inference(ennf_transformation,[],[f1])).
% 6.66/1.50  
% 6.66/1.50  fof(f17,plain,(
% 6.66/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.66/1.50    inference(nnf_transformation,[],[f14])).
% 6.66/1.50  
% 6.66/1.50  fof(f18,plain,(
% 6.66/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.66/1.50    inference(rectify,[],[f17])).
% 6.66/1.50  
% 6.66/1.50  fof(f19,plain,(
% 6.66/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.66/1.50    introduced(choice_axiom,[])).
% 6.66/1.50  
% 6.66/1.50  fof(f20,plain,(
% 6.66/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 6.66/1.50  
% 6.66/1.50  fof(f36,plain,(
% 6.66/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f20])).
% 6.66/1.50  
% 6.66/1.50  fof(f6,axiom,(
% 6.66/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f30,plain,(
% 6.66/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.66/1.50    inference(nnf_transformation,[],[f6])).
% 6.66/1.50  
% 6.66/1.50  fof(f31,plain,(
% 6.66/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.66/1.50    inference(rectify,[],[f30])).
% 6.66/1.50  
% 6.66/1.50  fof(f32,plain,(
% 6.66/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 6.66/1.50    introduced(choice_axiom,[])).
% 6.66/1.50  
% 6.66/1.50  fof(f33,plain,(
% 6.66/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 6.66/1.50  
% 6.66/1.50  fof(f52,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f33])).
% 6.66/1.50  
% 6.66/1.50  fof(f7,axiom,(
% 6.66/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f54,plain,(
% 6.66/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f7])).
% 6.66/1.50  
% 6.66/1.50  fof(f8,axiom,(
% 6.66/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f55,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f8])).
% 6.66/1.50  
% 6.66/1.50  fof(f9,axiom,(
% 6.66/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f56,plain,(
% 6.66/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f9])).
% 6.66/1.50  
% 6.66/1.50  fof(f10,axiom,(
% 6.66/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f57,plain,(
% 6.66/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f10])).
% 6.66/1.50  
% 6.66/1.50  fof(f63,plain,(
% 6.66/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.66/1.50    inference(definition_unfolding,[],[f56,f57])).
% 6.66/1.50  
% 6.66/1.50  fof(f64,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.66/1.50    inference(definition_unfolding,[],[f55,f63])).
% 6.66/1.50  
% 6.66/1.50  fof(f66,plain,(
% 6.66/1.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.66/1.50    inference(definition_unfolding,[],[f54,f64])).
% 6.66/1.50  
% 6.66/1.50  fof(f75,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 6.66/1.50    inference(definition_unfolding,[],[f52,f66])).
% 6.66/1.50  
% 6.66/1.50  fof(f12,conjecture,(
% 6.66/1.50    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f13,negated_conjecture,(
% 6.66/1.50    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.66/1.50    inference(negated_conjecture,[],[f12])).
% 6.66/1.50  
% 6.66/1.50  fof(f16,plain,(
% 6.66/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.66/1.50    inference(ennf_transformation,[],[f13])).
% 6.66/1.50  
% 6.66/1.50  fof(f34,plain,(
% 6.66/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & sK5 != sK6 & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 6.66/1.50    introduced(choice_axiom,[])).
% 6.66/1.50  
% 6.66/1.50  fof(f35,plain,(
% 6.66/1.50    k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & sK5 != sK6 & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 6.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f34])).
% 6.66/1.50  
% 6.66/1.50  fof(f59,plain,(
% 6.66/1.50    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 6.66/1.50    inference(cnf_transformation,[],[f35])).
% 6.66/1.50  
% 6.66/1.50  fof(f11,axiom,(
% 6.66/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f58,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.66/1.50    inference(cnf_transformation,[],[f11])).
% 6.66/1.50  
% 6.66/1.50  fof(f65,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.66/1.50    inference(definition_unfolding,[],[f58,f64])).
% 6.66/1.50  
% 6.66/1.50  fof(f78,plain,(
% 6.66/1.50    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))),
% 6.66/1.50    inference(definition_unfolding,[],[f59,f65,f66])).
% 6.66/1.50  
% 6.66/1.50  fof(f2,axiom,(
% 6.66/1.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f21,plain,(
% 6.66/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.66/1.50    inference(nnf_transformation,[],[f2])).
% 6.66/1.50  
% 6.66/1.50  fof(f22,plain,(
% 6.66/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.66/1.50    inference(flattening,[],[f21])).
% 6.66/1.50  
% 6.66/1.50  fof(f23,plain,(
% 6.66/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.66/1.50    inference(rectify,[],[f22])).
% 6.66/1.50  
% 6.66/1.50  fof(f24,plain,(
% 6.66/1.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 6.66/1.50    introduced(choice_axiom,[])).
% 6.66/1.50  
% 6.66/1.50  fof(f25,plain,(
% 6.66/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 6.66/1.50  
% 6.66/1.50  fof(f41,plain,(
% 6.66/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 6.66/1.50    inference(cnf_transformation,[],[f25])).
% 6.66/1.50  
% 6.66/1.50  fof(f70,plain,(
% 6.66/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 6.66/1.50    inference(definition_unfolding,[],[f41,f65])).
% 6.66/1.50  
% 6.66/1.50  fof(f79,plain,(
% 6.66/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 6.66/1.50    inference(equality_resolution,[],[f70])).
% 6.66/1.50  
% 6.66/1.50  fof(f50,plain,(
% 6.66/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.66/1.50    inference(cnf_transformation,[],[f33])).
% 6.66/1.50  
% 6.66/1.50  fof(f77,plain,(
% 6.66/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 6.66/1.50    inference(definition_unfolding,[],[f50,f66])).
% 6.66/1.50  
% 6.66/1.50  fof(f86,plain,(
% 6.66/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 6.66/1.50    inference(equality_resolution,[],[f77])).
% 6.66/1.50  
% 6.66/1.50  fof(f40,plain,(
% 6.66/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 6.66/1.50    inference(cnf_transformation,[],[f25])).
% 6.66/1.50  
% 6.66/1.50  fof(f71,plain,(
% 6.66/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 6.66/1.50    inference(definition_unfolding,[],[f40,f65])).
% 6.66/1.50  
% 6.66/1.50  fof(f80,plain,(
% 6.66/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 6.66/1.50    inference(equality_resolution,[],[f71])).
% 6.66/1.50  
% 6.66/1.50  fof(f4,axiom,(
% 6.66/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f28,plain,(
% 6.66/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.66/1.50    inference(nnf_transformation,[],[f4])).
% 6.66/1.50  
% 6.66/1.50  fof(f29,plain,(
% 6.66/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.66/1.50    inference(flattening,[],[f28])).
% 6.66/1.50  
% 6.66/1.50  fof(f46,plain,(
% 6.66/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.66/1.50    inference(cnf_transformation,[],[f29])).
% 6.66/1.50  
% 6.66/1.50  fof(f83,plain,(
% 6.66/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.66/1.50    inference(equality_resolution,[],[f46])).
% 6.66/1.50  
% 6.66/1.50  fof(f37,plain,(
% 6.66/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f20])).
% 6.66/1.50  
% 6.66/1.50  fof(f38,plain,(
% 6.66/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f20])).
% 6.66/1.50  
% 6.66/1.50  fof(f48,plain,(
% 6.66/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f29])).
% 6.66/1.50  
% 6.66/1.50  fof(f60,plain,(
% 6.66/1.50    sK5 != sK6),
% 6.66/1.50    inference(cnf_transformation,[],[f35])).
% 6.66/1.50  
% 6.66/1.50  fof(f61,plain,(
% 6.66/1.50    k1_xboole_0 != sK5),
% 6.66/1.50    inference(cnf_transformation,[],[f35])).
% 6.66/1.50  
% 6.66/1.50  fof(f51,plain,(
% 6.66/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 6.66/1.50    inference(cnf_transformation,[],[f33])).
% 6.66/1.50  
% 6.66/1.50  fof(f76,plain,(
% 6.66/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 6.66/1.50    inference(definition_unfolding,[],[f51,f66])).
% 6.66/1.50  
% 6.66/1.50  fof(f84,plain,(
% 6.66/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 6.66/1.50    inference(equality_resolution,[],[f76])).
% 6.66/1.50  
% 6.66/1.50  fof(f85,plain,(
% 6.66/1.50    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 6.66/1.50    inference(equality_resolution,[],[f84])).
% 6.66/1.50  
% 6.66/1.50  fof(f5,axiom,(
% 6.66/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.66/1.50  
% 6.66/1.50  fof(f49,plain,(
% 6.66/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.66/1.50    inference(cnf_transformation,[],[f5])).
% 6.66/1.50  
% 6.66/1.50  fof(f73,plain,(
% 6.66/1.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 6.66/1.50    inference(definition_unfolding,[],[f49,f65])).
% 6.66/1.50  
% 6.66/1.50  fof(f53,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 6.66/1.50    inference(cnf_transformation,[],[f33])).
% 6.66/1.50  
% 6.66/1.50  fof(f74,plain,(
% 6.66/1.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 6.66/1.50    inference(definition_unfolding,[],[f53,f66])).
% 6.66/1.50  
% 6.66/1.50  fof(f62,plain,(
% 6.66/1.50    k1_xboole_0 != sK6),
% 6.66/1.50    inference(cnf_transformation,[],[f35])).
% 6.66/1.50  
% 6.66/1.50  cnf(c_9,plain,
% 6.66/1.50      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 6.66/1.50      inference(cnf_transformation,[],[f45]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_610,plain,
% 6.66/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_2,plain,
% 6.66/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.66/1.50      inference(cnf_transformation,[],[f36]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_617,plain,
% 6.66/1.50      ( r2_hidden(X0,X1) != iProver_top
% 6.66/1.50      | r2_hidden(X0,X2) = iProver_top
% 6.66/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_1850,plain,
% 6.66/1.50      ( k1_xboole_0 = X0
% 6.66/1.50      | r2_hidden(sK2(X0),X1) = iProver_top
% 6.66/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_610,c_617]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_15,plain,
% 6.66/1.50      ( r2_hidden(sK3(X0,X1),X1)
% 6.66/1.50      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 6.66/1.50      | sK3(X0,X1) = X0 ),
% 6.66/1.50      inference(cnf_transformation,[],[f75]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_605,plain,
% 6.66/1.50      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 6.66/1.50      | sK3(X0,X1) = X0
% 6.66/1.50      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_21,negated_conjecture,
% 6.66/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 6.66/1.50      inference(cnf_transformation,[],[f78]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_6,plain,
% 6.66/1.50      ( ~ r2_hidden(X0,X1)
% 6.66/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 6.66/1.50      inference(cnf_transformation,[],[f79]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_613,plain,
% 6.66/1.50      ( r2_hidden(X0,X1) != iProver_top
% 6.66/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_1717,plain,
% 6.66/1.50      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 6.66/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_21,c_613]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_17,plain,
% 6.66/1.50      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 6.66/1.50      inference(cnf_transformation,[],[f86]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_603,plain,
% 6.66/1.50      ( X0 = X1
% 6.66/1.50      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_1830,plain,
% 6.66/1.50      ( sK4 = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_1717,c_603]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_2250,plain,
% 6.66/1.50      ( k3_enumset1(X0,X0,X0,X0,X0) = sK6
% 6.66/1.50      | sK3(X0,sK6) = X0
% 6.66/1.50      | sK3(X0,sK6) = sK4 ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_605,c_1830]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_7,plain,
% 6.66/1.50      ( ~ r2_hidden(X0,X1)
% 6.66/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
% 6.66/1.50      inference(cnf_transformation,[],[f80]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_612,plain,
% 6.66/1.50      ( r2_hidden(X0,X1) != iProver_top
% 6.66/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_1279,plain,
% 6.66/1.50      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 6.66/1.50      | r2_hidden(X0,sK5) != iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_21,c_612]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_10447,plain,
% 6.66/1.50      ( sK3(sK4,sK6) = sK4
% 6.66/1.50      | r2_hidden(X0,sK5) != iProver_top
% 6.66/1.50      | r2_hidden(X0,sK6) = iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_2250,c_1279]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_11193,plain,
% 6.66/1.50      ( sK3(sK4,sK6) = sK4
% 6.66/1.50      | k1_xboole_0 = X0
% 6.66/1.50      | r2_hidden(sK2(X0),sK6) = iProver_top
% 6.66/1.50      | r1_tarski(X0,sK5) != iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_1850,c_10447]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_12,plain,
% 6.66/1.50      ( r1_tarski(X0,X0) ),
% 6.66/1.50      inference(cnf_transformation,[],[f83]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_927,plain,
% 6.66/1.50      ( r1_tarski(sK6,sK6) ),
% 6.66/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_930,plain,
% 6.66/1.50      ( r1_tarski(sK6,sK6) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_1,plain,
% 6.66/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.66/1.50      inference(cnf_transformation,[],[f37]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_618,plain,
% 6.66/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 6.66/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_0,plain,
% 6.66/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 6.66/1.50      inference(cnf_transformation,[],[f38]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_619,plain,
% 6.66/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 6.66/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 6.66/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.66/1.50  
% 6.66/1.50  cnf(c_1829,plain,
% 6.66/1.50      ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
% 6.66/1.50      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 6.66/1.50      inference(superposition,[status(thm)],[c_1717,c_619]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_2350,plain,
% 6.66/1.51      ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_618,c_1829]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_10,plain,
% 6.66/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 6.66/1.51      inference(cnf_transformation,[],[f48]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_609,plain,
% 6.66/1.51      ( X0 = X1
% 6.66/1.51      | r1_tarski(X1,X0) != iProver_top
% 6.66/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 6.66/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_2490,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 6.66/1.51      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_2350,c_609]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_20,negated_conjecture,
% 6.66/1.51      ( sK5 != sK6 ),
% 6.66/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_19,negated_conjecture,
% 6.66/1.51      ( k1_xboole_0 != sK5 ),
% 6.66/1.51      inference(cnf_transformation,[],[f61]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_23,plain,
% 6.66/1.51      ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_16,plain,
% 6.66/1.51      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 6.66/1.51      inference(cnf_transformation,[],[f85]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_26,plain,
% 6.66/1.51      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_316,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_756,plain,
% 6.66/1.51      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_316]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_879,plain,
% 6.66/1.51      ( sK5 != k1_xboole_0
% 6.66/1.51      | k1_xboole_0 = sK5
% 6.66/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_756]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_315,plain,( X0 = X0 ),theory(equality) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_880,plain,
% 6.66/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_315]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_854,plain,
% 6.66/1.51      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_926,plain,
% 6.66/1.51      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_854]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_13,plain,
% 6.66/1.51      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 6.66/1.51      inference(cnf_transformation,[],[f73]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_607,plain,
% 6.66/1.51      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 6.66/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_898,plain,
% 6.66/1.51      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_21,c_607]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1234,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 6.66/1.51      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_898,c_609]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1297,plain,
% 6.66/1.51      ( sK4 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_1279,c_603]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1384,plain,
% 6.66/1.51      ( sK2(sK5) = sK4 | sK5 = k1_xboole_0 ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_610,c_1297]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1509,plain,
% 6.66/1.51      ( sK2(sK5) = sK4 ),
% 6.66/1.51      inference(global_propositional_subsumption,
% 6.66/1.51                [status(thm)],
% 6.66/1.51                [c_1384,c_19,c_879,c_880]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1512,plain,
% 6.66/1.51      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK5) = iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_1509,c_610]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_859,plain,
% 6.66/1.51      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_316]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_960,plain,
% 6.66/1.51      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_859]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_4736,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
% 6.66/1.51      | sK6 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 6.66/1.51      | sK6 != sK6 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_960]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1143,plain,
% 6.66/1.51      ( X0 != X1
% 6.66/1.51      | X0 = k3_enumset1(X2,X2,X2,X2,X2)
% 6.66/1.51      | k3_enumset1(X2,X2,X2,X2,X2) != X1 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_316]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_4738,plain,
% 6.66/1.51      ( X0 != X1
% 6.66/1.51      | X0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 6.66/1.51      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_1143]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_4739,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
% 6.66/1.51      | sK5 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 6.66/1.51      | sK5 != sK5 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_4738]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1152,plain,
% 6.66/1.51      ( sK0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X0
% 6.66/1.51      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_618,c_603]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_6378,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 6.66/1.51      | sK0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = sK4 ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_1152,c_1234]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_8259,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 6.66/1.51      | r2_hidden(sK4,sK5) != iProver_top
% 6.66/1.51      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_6378,c_619]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_757,plain,
% 6.66/1.51      ( sK5 != X0 | sK5 = sK6 | sK6 != X0 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_316]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_12175,plain,
% 6.66/1.51      ( sK5 != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 6.66/1.51      | sK5 = sK6
% 6.66/1.51      | sK6 != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_757]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_17203,plain,
% 6.66/1.51      ( r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
% 6.66/1.51      inference(global_propositional_subsumption,
% 6.66/1.51                [status(thm)],
% 6.66/1.51                [c_2490,c_20,c_19,c_23,c_26,c_879,c_880,c_926,c_927,
% 6.66/1.51                 c_1234,c_1512,c_4736,c_4739,c_8259,c_12175]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_17210,plain,
% 6.66/1.51      ( sK3(sK4,sK6) = sK4 | r1_tarski(sK6,sK6) != iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_2250,c_17203]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_27620,plain,
% 6.66/1.51      ( sK3(sK4,sK6) = sK4 ),
% 6.66/1.51      inference(global_propositional_subsumption,
% 6.66/1.51                [status(thm)],
% 6.66/1.51                [c_11193,c_930,c_17210]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_14,plain,
% 6.66/1.51      ( ~ r2_hidden(sK3(X0,X1),X1)
% 6.66/1.51      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 6.66/1.51      | sK3(X0,X1) != X0 ),
% 6.66/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_606,plain,
% 6.66/1.51      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 6.66/1.51      | sK3(X0,X1) != X0
% 6.66/1.51      | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
% 6.66/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_27624,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 6.66/1.51      | r2_hidden(sK3(sK4,sK6),sK6) != iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_27620,c_606]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_27629,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 6.66/1.51      | r2_hidden(sK4,sK6) != iProver_top ),
% 6.66/1.51      inference(light_normalisation,[status(thm)],[c_27624,c_27620]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_1699,plain,
% 6.66/1.51      ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
% 6.66/1.51      | sK3(X0,sK5) = X0
% 6.66/1.51      | sK3(X0,sK5) = sK4 ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_605,c_1297]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_8357,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 6.66/1.51      | sK3(sK4,sK5) = sK4
% 6.66/1.51      | r1_tarski(sK5,sK5) != iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_1699,c_1234]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_21213,plain,
% 6.66/1.51      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5 ),
% 6.66/1.51      inference(global_propositional_subsumption,
% 6.66/1.51                [status(thm)],
% 6.66/1.51                [c_8357,c_19,c_879,c_880,c_1234,c_1512,c_8259]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_27630,plain,
% 6.66/1.51      ( sK5 = sK6 | r2_hidden(sK4,sK6) != iProver_top ),
% 6.66/1.51      inference(demodulation,[status(thm)],[c_27629,c_21213]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_755,plain,
% 6.66/1.51      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_316]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_6438,plain,
% 6.66/1.51      ( sK6 != k1_xboole_0
% 6.66/1.51      | k1_xboole_0 = sK6
% 6.66/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 6.66/1.51      inference(instantiation,[status(thm)],[c_755]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_2249,plain,
% 6.66/1.51      ( sK2(sK6) = sK4 | sK6 = k1_xboole_0 ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_610,c_1830]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_2638,plain,
% 6.66/1.51      ( sK6 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 6.66/1.51      inference(superposition,[status(thm)],[c_2249,c_610]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(c_18,negated_conjecture,
% 6.66/1.51      ( k1_xboole_0 != sK6 ),
% 6.66/1.51      inference(cnf_transformation,[],[f62]) ).
% 6.66/1.51  
% 6.66/1.51  cnf(contradiction,plain,
% 6.66/1.51      ( $false ),
% 6.66/1.51      inference(minisat,
% 6.66/1.51                [status(thm)],
% 6.66/1.51                [c_27630,c_6438,c_2638,c_880,c_18,c_20]) ).
% 6.66/1.51  
% 6.66/1.51  
% 6.66/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.66/1.51  
% 6.66/1.51  ------                               Statistics
% 6.66/1.51  
% 6.66/1.51  ------ General
% 6.66/1.51  
% 6.66/1.51  abstr_ref_over_cycles:                  0
% 6.66/1.51  abstr_ref_under_cycles:                 0
% 6.66/1.51  gc_basic_clause_elim:                   0
% 6.66/1.51  forced_gc_time:                         0
% 6.66/1.51  parsing_time:                           0.014
% 6.66/1.51  unif_index_cands_time:                  0.
% 6.66/1.51  unif_index_add_time:                    0.
% 6.66/1.51  orderings_time:                         0.
% 6.66/1.51  out_proof_time:                         0.013
% 6.66/1.51  total_time:                             0.677
% 6.66/1.51  num_of_symbols:                         43
% 6.66/1.51  num_of_terms:                           21027
% 6.66/1.51  
% 6.66/1.51  ------ Preprocessing
% 6.66/1.51  
% 6.66/1.51  num_of_splits:                          0
% 6.66/1.51  num_of_split_atoms:                     0
% 6.66/1.51  num_of_reused_defs:                     0
% 6.66/1.51  num_eq_ax_congr_red:                    27
% 6.66/1.51  num_of_sem_filtered_clauses:            1
% 6.66/1.51  num_of_subtypes:                        0
% 6.66/1.51  monotx_restored_types:                  0
% 6.66/1.51  sat_num_of_epr_types:                   0
% 6.66/1.51  sat_num_of_non_cyclic_types:            0
% 6.66/1.51  sat_guarded_non_collapsed_types:        0
% 6.66/1.51  num_pure_diseq_elim:                    0
% 6.66/1.51  simp_replaced_by:                       0
% 6.66/1.51  res_preprocessed:                       97
% 6.66/1.51  prep_upred:                             0
% 6.66/1.51  prep_unflattend:                        0
% 6.66/1.51  smt_new_axioms:                         0
% 6.66/1.51  pred_elim_cands:                        2
% 6.66/1.51  pred_elim:                              0
% 6.66/1.51  pred_elim_cl:                           0
% 6.66/1.51  pred_elim_cycles:                       2
% 6.66/1.51  merged_defs:                            0
% 6.66/1.51  merged_defs_ncl:                        0
% 6.66/1.51  bin_hyper_res:                          0
% 6.66/1.51  prep_cycles:                            4
% 6.66/1.51  pred_elim_time:                         0.
% 6.66/1.51  splitting_time:                         0.
% 6.66/1.51  sem_filter_time:                        0.
% 6.66/1.51  monotx_time:                            0.
% 6.66/1.51  subtype_inf_time:                       0.
% 6.66/1.51  
% 6.66/1.51  ------ Problem properties
% 6.66/1.51  
% 6.66/1.51  clauses:                                21
% 6.66/1.51  conjectures:                            4
% 6.66/1.51  epr:                                    6
% 6.66/1.51  horn:                                   16
% 6.66/1.51  ground:                                 4
% 6.66/1.51  unary:                                  7
% 6.66/1.51  binary:                                 6
% 6.66/1.51  lits:                                   44
% 6.66/1.51  lits_eq:                                14
% 6.66/1.51  fd_pure:                                0
% 6.66/1.51  fd_pseudo:                              0
% 6.66/1.51  fd_cond:                                1
% 6.66/1.51  fd_pseudo_cond:                         6
% 6.66/1.51  ac_symbols:                             0
% 6.66/1.51  
% 6.66/1.51  ------ Propositional Solver
% 6.66/1.51  
% 6.66/1.51  prop_solver_calls:                      29
% 6.66/1.51  prop_fast_solver_calls:                 914
% 6.66/1.51  smt_solver_calls:                       0
% 6.66/1.51  smt_fast_solver_calls:                  0
% 6.66/1.51  prop_num_of_clauses:                    9305
% 6.66/1.51  prop_preprocess_simplified:             19603
% 6.66/1.51  prop_fo_subsumed:                       21
% 6.66/1.51  prop_solver_time:                       0.
% 6.66/1.51  smt_solver_time:                        0.
% 6.66/1.51  smt_fast_solver_time:                   0.
% 6.66/1.51  prop_fast_solver_time:                  0.
% 6.66/1.51  prop_unsat_core_time:                   0.
% 6.66/1.51  
% 6.66/1.51  ------ QBF
% 6.66/1.51  
% 6.66/1.51  qbf_q_res:                              0
% 6.66/1.51  qbf_num_tautologies:                    0
% 6.66/1.51  qbf_prep_cycles:                        0
% 6.66/1.51  
% 6.66/1.51  ------ BMC1
% 6.66/1.51  
% 6.66/1.51  bmc1_current_bound:                     -1
% 6.66/1.51  bmc1_last_solved_bound:                 -1
% 6.66/1.51  bmc1_unsat_core_size:                   -1
% 6.66/1.51  bmc1_unsat_core_parents_size:           -1
% 6.66/1.51  bmc1_merge_next_fun:                    0
% 6.66/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.66/1.51  
% 6.66/1.51  ------ Instantiation
% 6.66/1.51  
% 6.66/1.51  inst_num_of_clauses:                    2087
% 6.66/1.51  inst_num_in_passive:                    1548
% 6.66/1.51  inst_num_in_active:                     518
% 6.66/1.51  inst_num_in_unprocessed:                21
% 6.66/1.51  inst_num_of_loops:                      850
% 6.66/1.51  inst_num_of_learning_restarts:          0
% 6.66/1.51  inst_num_moves_active_passive:          331
% 6.66/1.51  inst_lit_activity:                      0
% 6.66/1.51  inst_lit_activity_moves:                0
% 6.66/1.51  inst_num_tautologies:                   0
% 6.66/1.51  inst_num_prop_implied:                  0
% 6.66/1.51  inst_num_existing_simplified:           0
% 6.66/1.51  inst_num_eq_res_simplified:             0
% 6.66/1.51  inst_num_child_elim:                    0
% 6.66/1.51  inst_num_of_dismatching_blockings:      1458
% 6.66/1.51  inst_num_of_non_proper_insts:           2179
% 6.66/1.51  inst_num_of_duplicates:                 0
% 6.66/1.51  inst_inst_num_from_inst_to_res:         0
% 6.66/1.51  inst_dismatching_checking_time:         0.
% 6.66/1.51  
% 6.66/1.51  ------ Resolution
% 6.66/1.51  
% 6.66/1.51  res_num_of_clauses:                     0
% 6.66/1.51  res_num_in_passive:                     0
% 6.66/1.51  res_num_in_active:                      0
% 6.66/1.51  res_num_of_loops:                       101
% 6.66/1.51  res_forward_subset_subsumed:            191
% 6.66/1.51  res_backward_subset_subsumed:           2
% 6.66/1.51  res_forward_subsumed:                   0
% 6.66/1.51  res_backward_subsumed:                  0
% 6.66/1.51  res_forward_subsumption_resolution:     0
% 6.66/1.51  res_backward_subsumption_resolution:    0
% 6.66/1.51  res_clause_to_clause_subsumption:       6869
% 6.66/1.51  res_orphan_elimination:                 0
% 6.66/1.51  res_tautology_del:                      124
% 6.66/1.51  res_num_eq_res_simplified:              0
% 6.66/1.51  res_num_sel_changes:                    0
% 6.66/1.51  res_moves_from_active_to_pass:          0
% 6.66/1.51  
% 6.66/1.51  ------ Superposition
% 6.66/1.51  
% 6.66/1.51  sup_time_total:                         0.
% 6.66/1.51  sup_time_generating:                    0.
% 6.66/1.51  sup_time_sim_full:                      0.
% 6.66/1.51  sup_time_sim_immed:                     0.
% 6.66/1.51  
% 6.66/1.51  sup_num_of_clauses:                     945
% 6.66/1.51  sup_num_in_active:                      101
% 6.66/1.51  sup_num_in_passive:                     844
% 6.66/1.51  sup_num_of_loops:                       169
% 6.66/1.51  sup_fw_superposition:                   739
% 6.66/1.51  sup_bw_superposition:                   991
% 6.66/1.51  sup_immediate_simplified:               362
% 6.66/1.51  sup_given_eliminated:                   1
% 6.66/1.51  comparisons_done:                       0
% 6.66/1.51  comparisons_avoided:                    38
% 6.66/1.51  
% 6.66/1.51  ------ Simplifications
% 6.66/1.51  
% 6.66/1.51  
% 6.66/1.51  sim_fw_subset_subsumed:                 138
% 6.66/1.51  sim_bw_subset_subsumed:                 89
% 6.66/1.51  sim_fw_subsumed:                        151
% 6.66/1.51  sim_bw_subsumed:                        5
% 6.66/1.51  sim_fw_subsumption_res:                 50
% 6.66/1.51  sim_bw_subsumption_res:                 0
% 6.66/1.51  sim_tautology_del:                      100
% 6.66/1.51  sim_eq_tautology_del:                   9
% 6.66/1.51  sim_eq_res_simp:                        27
% 6.66/1.51  sim_fw_demodulated:                     11
% 6.66/1.51  sim_bw_demodulated:                     61
% 6.66/1.51  sim_light_normalised:                   33
% 6.66/1.51  sim_joinable_taut:                      0
% 6.66/1.51  sim_joinable_simp:                      0
% 6.66/1.51  sim_ac_normalised:                      0
% 6.66/1.51  sim_smt_subsumption:                    0
% 6.66/1.51  
%------------------------------------------------------------------------------
