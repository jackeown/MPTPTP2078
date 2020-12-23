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
% DateTime   : Thu Dec  3 11:32:35 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 767 expanded)
%              Number of clauses        :   81 ( 150 expanded)
%              Number of leaves         :   18 ( 209 expanded)
%              Depth                    :   16
%              Number of atoms          :  421 (2207 expanded)
%              Number of equality atoms :  252 (1179 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f94,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,
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

fof(f38,plain,
    ( k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & sK5 != sK6
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f37])).

fof(f65,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f86,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f65,f71,f72])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f29])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f92,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f84])).

fof(f93,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f92])).

fof(f66,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_242,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_23515,plain,
    ( sK5 != X0
    | sK5 = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_27866,plain,
    ( sK5 != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK5 = sK6
    | sK6 != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_23515])).

cnf(c_25238,plain,
    ( X0 != X1
    | X0 = k3_enumset1(X2,X3,X4,X5,X6)
    | k3_enumset1(X2,X3,X4,X5,X6) != X1 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_27439,plain,
    ( k3_enumset1(X0,X1,X2,X3,X4) != X5
    | sK6 != X5
    | sK6 = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_25238])).

cnf(c_27693,plain,
    ( k3_enumset1(X0,X1,X2,X3,X4) != sK6
    | sK6 = k3_enumset1(X0,X1,X2,X3,X4)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_27439])).

cnf(c_27694,plain,
    ( k3_enumset1(X0,X1,X2,X3,X4) != sK6
    | sK6 = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(equality_resolution_simp,[status(thm)],[c_27693])).

cnf(c_27754,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | sK6 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_27694])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23371,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_23365,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23774,plain,
    ( sK0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X0
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_23371,c_23365])).

cnf(c_23,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23370,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24539,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_23370])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23372,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_24712,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24539,c_23372])).

cnf(c_24902,plain,
    ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23371,c_24712])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23367,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_24991,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24902,c_23367])).

cnf(c_25792,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | sK0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) = sK4 ),
    inference(superposition,[status(thm)],[c_23774,c_24991])).

cnf(c_26400,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | r2_hidden(sK4,sK6) != iProver_top
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_25792,c_23372])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23369,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_23899,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_23369])).

cnf(c_24055,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK5) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23899,c_23372])).

cnf(c_24179,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23371,c_24055])).

cnf(c_24183,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_24179,c_23367])).

cnf(c_25791,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | sK0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_23774,c_24183])).

cnf(c_26386,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_25791,c_23372])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23368,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_24713,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24539,c_23365])).

cnf(c_24889,plain,
    ( sK2(sK6) = sK4
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23368,c_24713])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_884,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_889,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_890,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_889])).

cnf(c_24993,plain,
    ( sK2(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24889,c_20,c_890])).

cnf(c_24996,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_24993,c_23368])).

cnf(c_24056,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_23899,c_23365])).

cnf(c_24071,plain,
    ( sK2(sK5) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23368,c_24056])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_885,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_892,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_893,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_892])).

cnf(c_24309,plain,
    ( sK2(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24071,c_21,c_893])).

cnf(c_24312,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_24309,c_23368])).

cnf(c_6679,plain,
    ( X0 != X1
    | X0 = k3_enumset1(X2,X2,X2,X2,X2)
    | k3_enumset1(X2,X2,X2,X2,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_14176,plain,
    ( X0 != X1
    | X0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_6679])).

cnf(c_14177,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
    | sK5 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_14176])).

cnf(c_7046,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_242,c_10])).

cnf(c_241,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7051,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_242,c_241])).

cnf(c_7737,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_7051,c_23])).

cnf(c_9119,plain,
    ( ~ r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)
    | X0 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_7046,c_7737])).

cnf(c_9120,plain,
    ( X0 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9119])).

cnf(c_9122,plain,
    ( sK5 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9120])).

cnf(c_5875,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5873,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7682,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_5873])).

cnf(c_5876,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7873,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7682,c_5876])).

cnf(c_8129,plain,
    ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5875,c_7873])).

cnf(c_5870,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8314,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8129,c_5870])).

cnf(c_5872,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6768,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_5872])).

cnf(c_6984,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK5) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6768,c_5876])).

cnf(c_7194,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5875,c_6984])).

cnf(c_6936,plain,
    ( X0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | X0 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_6679])).

cnf(c_6937,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | sK5 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK5 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_6936])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_28,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27866,c_27754,c_26400,c_26386,c_24996,c_24312,c_14177,c_9122,c_8314,c_7194,c_6937,c_893,c_890,c_28,c_25,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.76/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.50  
% 7.76/1.50  ------  iProver source info
% 7.76/1.50  
% 7.76/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.50  git: non_committed_changes: false
% 7.76/1.50  git: last_make_outside_of_git: false
% 7.76/1.50  
% 7.76/1.50  ------ 
% 7.76/1.50  ------ Parsing...
% 7.76/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  ------ Proving...
% 7.76/1.50  ------ Problem Properties 
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  clauses                                 23
% 7.76/1.50  conjectures                             4
% 7.76/1.50  EPR                                     6
% 7.76/1.50  Horn                                    18
% 7.76/1.50  unary                                   9
% 7.76/1.50  binary                                  6
% 7.76/1.50  lits                                    46
% 7.76/1.50  lits eq                                 17
% 7.76/1.50  fd_pure                                 0
% 7.76/1.50  fd_pseudo                               0
% 7.76/1.50  fd_cond                                 1
% 7.76/1.50  fd_pseudo_cond                          6
% 7.76/1.50  AC symbols                              0
% 7.76/1.50  
% 7.76/1.50  ------ Input Options Time Limit: Unbounded
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.76/1.50  Current options:
% 7.76/1.50  ------ 
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  % SZS status Theorem for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  fof(f1,axiom,(
% 7.76/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f17,plain,(
% 7.76/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.76/1.50    inference(ennf_transformation,[],[f1])).
% 7.76/1.50  
% 7.76/1.50  fof(f20,plain,(
% 7.76/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.76/1.50    inference(nnf_transformation,[],[f17])).
% 7.76/1.50  
% 7.76/1.50  fof(f21,plain,(
% 7.76/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.76/1.50    inference(rectify,[],[f20])).
% 7.76/1.50  
% 7.76/1.50  fof(f22,plain,(
% 7.76/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f23,plain,(
% 7.76/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 7.76/1.50  
% 7.76/1.50  fof(f40,plain,(
% 7.76/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f23])).
% 7.76/1.50  
% 7.76/1.50  fof(f9,axiom,(
% 7.76/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f33,plain,(
% 7.76/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.76/1.50    inference(nnf_transformation,[],[f9])).
% 7.76/1.50  
% 7.76/1.50  fof(f34,plain,(
% 7.76/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.76/1.50    inference(rectify,[],[f33])).
% 7.76/1.50  
% 7.76/1.50  fof(f35,plain,(
% 7.76/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f36,plain,(
% 7.76/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 7.76/1.50  
% 7.76/1.50  fof(f56,plain,(
% 7.76/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.76/1.50    inference(cnf_transformation,[],[f36])).
% 7.76/1.50  
% 7.76/1.50  fof(f10,axiom,(
% 7.76/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f60,plain,(
% 7.76/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f10])).
% 7.76/1.50  
% 7.76/1.50  fof(f11,axiom,(
% 7.76/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f61,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f11])).
% 7.76/1.50  
% 7.76/1.50  fof(f12,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f62,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f12])).
% 7.76/1.50  
% 7.76/1.50  fof(f13,axiom,(
% 7.76/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f63,plain,(
% 7.76/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f13])).
% 7.76/1.50  
% 7.76/1.50  fof(f69,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f62,f63])).
% 7.76/1.50  
% 7.76/1.50  fof(f70,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f61,f69])).
% 7.76/1.50  
% 7.76/1.50  fof(f72,plain,(
% 7.76/1.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f60,f70])).
% 7.76/1.50  
% 7.76/1.50  fof(f85,plain,(
% 7.76/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.76/1.50    inference(definition_unfolding,[],[f56,f72])).
% 7.76/1.50  
% 7.76/1.50  fof(f94,plain,(
% 7.76/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 7.76/1.50    inference(equality_resolution,[],[f85])).
% 7.76/1.50  
% 7.76/1.50  fof(f15,conjecture,(
% 7.76/1.50    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f16,negated_conjecture,(
% 7.76/1.50    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.76/1.50    inference(negated_conjecture,[],[f15])).
% 7.76/1.50  
% 7.76/1.50  fof(f19,plain,(
% 7.76/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.76/1.50    inference(ennf_transformation,[],[f16])).
% 7.76/1.50  
% 7.76/1.50  fof(f37,plain,(
% 7.76/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & sK5 != sK6 & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f38,plain,(
% 7.76/1.50    k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & sK5 != sK6 & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f37])).
% 7.76/1.50  
% 7.76/1.50  fof(f65,plain,(
% 7.76/1.50    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 7.76/1.50    inference(cnf_transformation,[],[f38])).
% 7.76/1.50  
% 7.76/1.50  fof(f14,axiom,(
% 7.76/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f64,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.76/1.50    inference(cnf_transformation,[],[f14])).
% 7.76/1.50  
% 7.76/1.50  fof(f71,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.76/1.50    inference(definition_unfolding,[],[f64,f70])).
% 7.76/1.50  
% 7.76/1.50  fof(f86,plain,(
% 7.76/1.50    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))),
% 7.76/1.50    inference(definition_unfolding,[],[f65,f71,f72])).
% 7.76/1.50  
% 7.76/1.50  fof(f2,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f24,plain,(
% 7.76/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.76/1.50    inference(nnf_transformation,[],[f2])).
% 7.76/1.50  
% 7.76/1.50  fof(f25,plain,(
% 7.76/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.76/1.50    inference(flattening,[],[f24])).
% 7.76/1.50  
% 7.76/1.50  fof(f26,plain,(
% 7.76/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.76/1.50    inference(rectify,[],[f25])).
% 7.76/1.50  
% 7.76/1.50  fof(f27,plain,(
% 7.76/1.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f28,plain,(
% 7.76/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 7.76/1.50  
% 7.76/1.50  fof(f44,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 7.76/1.50    inference(cnf_transformation,[],[f28])).
% 7.76/1.50  
% 7.76/1.50  fof(f76,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 7.76/1.50    inference(definition_unfolding,[],[f44,f71])).
% 7.76/1.50  
% 7.76/1.50  fof(f87,plain,(
% 7.76/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 7.76/1.50    inference(equality_resolution,[],[f76])).
% 7.76/1.50  
% 7.76/1.50  fof(f41,plain,(
% 7.76/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f23])).
% 7.76/1.50  
% 7.76/1.50  fof(f4,axiom,(
% 7.76/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f31,plain,(
% 7.76/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.76/1.50    inference(nnf_transformation,[],[f4])).
% 7.76/1.50  
% 7.76/1.50  fof(f32,plain,(
% 7.76/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.76/1.50    inference(flattening,[],[f31])).
% 7.76/1.50  
% 7.76/1.50  fof(f51,plain,(
% 7.76/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f32])).
% 7.76/1.50  
% 7.76/1.50  fof(f43,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.76/1.50    inference(cnf_transformation,[],[f28])).
% 7.76/1.50  
% 7.76/1.50  fof(f77,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 7.76/1.50    inference(definition_unfolding,[],[f43,f71])).
% 7.76/1.50  
% 7.76/1.50  fof(f88,plain,(
% 7.76/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 7.76/1.50    inference(equality_resolution,[],[f77])).
% 7.76/1.50  
% 7.76/1.50  fof(f3,axiom,(
% 7.76/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f18,plain,(
% 7.76/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.76/1.50    inference(ennf_transformation,[],[f3])).
% 7.76/1.50  
% 7.76/1.50  fof(f29,plain,(
% 7.76/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f30,plain,(
% 7.76/1.50    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f29])).
% 7.76/1.50  
% 7.76/1.50  fof(f48,plain,(
% 7.76/1.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.76/1.50    inference(cnf_transformation,[],[f30])).
% 7.76/1.50  
% 7.76/1.50  fof(f68,plain,(
% 7.76/1.50    k1_xboole_0 != sK6),
% 7.76/1.50    inference(cnf_transformation,[],[f38])).
% 7.76/1.50  
% 7.76/1.50  fof(f67,plain,(
% 7.76/1.50    k1_xboole_0 != sK5),
% 7.76/1.50    inference(cnf_transformation,[],[f38])).
% 7.76/1.50  
% 7.76/1.50  fof(f57,plain,(
% 7.76/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.76/1.50    inference(cnf_transformation,[],[f36])).
% 7.76/1.50  
% 7.76/1.50  fof(f84,plain,(
% 7.76/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.76/1.50    inference(definition_unfolding,[],[f57,f72])).
% 7.76/1.50  
% 7.76/1.50  fof(f92,plain,(
% 7.76/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 7.76/1.50    inference(equality_resolution,[],[f84])).
% 7.76/1.50  
% 7.76/1.50  fof(f93,plain,(
% 7.76/1.50    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 7.76/1.50    inference(equality_resolution,[],[f92])).
% 7.76/1.50  
% 7.76/1.50  fof(f66,plain,(
% 7.76/1.50    sK5 != sK6),
% 7.76/1.50    inference(cnf_transformation,[],[f38])).
% 7.76/1.50  
% 7.76/1.50  cnf(c_242,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23515,plain,
% 7.76/1.50      ( sK5 != X0 | sK5 = sK6 | sK6 != X0 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_242]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_27866,plain,
% 7.76/1.50      ( sK5 != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 7.76/1.50      | sK5 = sK6
% 7.76/1.50      | sK6 != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_23515]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25238,plain,
% 7.76/1.50      ( X0 != X1
% 7.76/1.50      | X0 = k3_enumset1(X2,X3,X4,X5,X6)
% 7.76/1.50      | k3_enumset1(X2,X3,X4,X5,X6) != X1 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_242]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_27439,plain,
% 7.76/1.50      ( k3_enumset1(X0,X1,X2,X3,X4) != X5
% 7.76/1.50      | sK6 != X5
% 7.76/1.50      | sK6 = k3_enumset1(X0,X1,X2,X3,X4) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_25238]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_27693,plain,
% 7.76/1.50      ( k3_enumset1(X0,X1,X2,X3,X4) != sK6
% 7.76/1.50      | sK6 = k3_enumset1(X0,X1,X2,X3,X4)
% 7.76/1.50      | sK6 != sK6 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_27439]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_27694,plain,
% 7.76/1.50      ( k3_enumset1(X0,X1,X2,X3,X4) != sK6
% 7.76/1.50      | sK6 = k3_enumset1(X0,X1,X2,X3,X4) ),
% 7.76/1.50      inference(equality_resolution_simp,[status(thm)],[c_27693]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_27754,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
% 7.76/1.50      | sK6 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_27694]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23371,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.76/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_19,plain,
% 7.76/1.50      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.76/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23365,plain,
% 7.76/1.50      ( X0 = X1
% 7.76/1.50      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23774,plain,
% 7.76/1.50      ( sK0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X0
% 7.76/1.50      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23371,c_23365]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23,negated_conjecture,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 7.76/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6,plain,
% 7.76/1.50      ( ~ r2_hidden(X0,X1)
% 7.76/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 7.76/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23370,plain,
% 7.76/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.76/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24539,plain,
% 7.76/1.50      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 7.76/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23,c_23370]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_0,plain,
% 7.76/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23372,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.76/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24712,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
% 7.76/1.50      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_24539,c_23372]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24902,plain,
% 7.76/1.50      ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23371,c_24712]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_10,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.76/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23367,plain,
% 7.76/1.50      ( X0 = X1
% 7.76/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.76/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24991,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_24902,c_23367]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25792,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 7.76/1.50      | sK0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) = sK4 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23774,c_24991]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_26400,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 7.76/1.50      | r2_hidden(sK4,sK6) != iProver_top
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_25792,c_23372]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7,plain,
% 7.76/1.50      ( ~ r2_hidden(X0,X1)
% 7.76/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
% 7.76/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23369,plain,
% 7.76/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.76/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23899,plain,
% 7.76/1.50      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 7.76/1.50      | r2_hidden(X0,sK5) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23,c_23369]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24055,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK5) != iProver_top
% 7.76/1.50      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23899,c_23372]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24179,plain,
% 7.76/1.50      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23371,c_24055]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24183,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_24179,c_23367]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25791,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 7.76/1.50      | sK0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = sK4 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23774,c_24183]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_26386,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 7.76/1.50      | r2_hidden(sK4,sK5) != iProver_top
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_25791,c_23372]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_9,plain,
% 7.76/1.50      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.76/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_23368,plain,
% 7.76/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24713,plain,
% 7.76/1.50      ( sK4 = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_24539,c_23365]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24889,plain,
% 7.76/1.50      ( sK2(sK6) = sK4 | sK6 = k1_xboole_0 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23368,c_24713]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_20,negated_conjecture,
% 7.76/1.50      ( k1_xboole_0 != sK6 ),
% 7.76/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_884,plain,
% 7.76/1.50      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_242]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_889,plain,
% 7.76/1.50      ( sK6 != k1_xboole_0
% 7.76/1.50      | k1_xboole_0 = sK6
% 7.76/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_884]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_890,plain,
% 7.76/1.50      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 ),
% 7.76/1.50      inference(equality_resolution_simp,[status(thm)],[c_889]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24993,plain,
% 7.76/1.50      ( sK2(sK6) = sK4 ),
% 7.76/1.50      inference(global_propositional_subsumption,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_24889,c_20,c_890]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24996,plain,
% 7.76/1.50      ( sK6 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_24993,c_23368]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24056,plain,
% 7.76/1.50      ( sK4 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23899,c_23365]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24071,plain,
% 7.76/1.50      ( sK2(sK5) = sK4 | sK5 = k1_xboole_0 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23368,c_24056]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_21,negated_conjecture,
% 7.76/1.50      ( k1_xboole_0 != sK5 ),
% 7.76/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_885,plain,
% 7.76/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_242]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_892,plain,
% 7.76/1.50      ( sK5 != k1_xboole_0
% 7.76/1.50      | k1_xboole_0 = sK5
% 7.76/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_885]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_893,plain,
% 7.76/1.50      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 ),
% 7.76/1.50      inference(equality_resolution_simp,[status(thm)],[c_892]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24309,plain,
% 7.76/1.50      ( sK2(sK5) = sK4 ),
% 7.76/1.50      inference(global_propositional_subsumption,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_24071,c_21,c_893]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24312,plain,
% 7.76/1.50      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK5) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_24309,c_23368]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6679,plain,
% 7.76/1.50      ( X0 != X1
% 7.76/1.50      | X0 = k3_enumset1(X2,X2,X2,X2,X2)
% 7.76/1.50      | k3_enumset1(X2,X2,X2,X2,X2) != X1 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_242]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_14176,plain,
% 7.76/1.50      ( X0 != X1
% 7.76/1.50      | X0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 7.76/1.50      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_6679]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_14177,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
% 7.76/1.50      | sK5 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 7.76/1.50      | sK5 != sK5 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_14176]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7046,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 7.76/1.50      inference(resolution,[status(thm)],[c_242,c_10]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_241,plain,( X0 = X0 ),theory(equality) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7051,plain,
% 7.76/1.50      ( X0 != X1 | X1 = X0 ),
% 7.76/1.50      inference(resolution,[status(thm)],[c_242,c_241]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7737,plain,
% 7.76/1.50      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 7.76/1.50      inference(resolution,[status(thm)],[c_7051,c_23]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_9119,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 7.76/1.50      | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)
% 7.76/1.50      | X0 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 7.76/1.50      inference(resolution,[status(thm)],[c_7046,c_7737]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_9120,plain,
% 7.76/1.50      ( X0 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 7.76/1.50      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_9119]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_9122,plain,
% 7.76/1.50      ( sK5 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 7.76/1.50      | r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_9120]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5875,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.76/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5873,plain,
% 7.76/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.76/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7682,plain,
% 7.76/1.50      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 7.76/1.50      | r2_hidden(X0,sK6) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23,c_5873]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5876,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.76/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7873,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
% 7.76/1.50      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_7682,c_5876]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_8129,plain,
% 7.76/1.50      ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_5875,c_7873]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5870,plain,
% 7.76/1.50      ( X0 = X1
% 7.76/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.76/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_8314,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 7.76/1.50      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_8129,c_5870]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5872,plain,
% 7.76/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.76/1.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6768,plain,
% 7.76/1.50      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 7.76/1.50      | r2_hidden(X0,sK5) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_23,c_5872]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6984,plain,
% 7.76/1.50      ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK5) != iProver_top
% 7.76/1.50      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_6768,c_5876]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7194,plain,
% 7.76/1.50      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_5875,c_6984]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6936,plain,
% 7.76/1.50      ( X0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 7.76/1.50      | X0 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 7.76/1.50      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_6679]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6937,plain,
% 7.76/1.50      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 7.76/1.50      | sK5 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 7.76/1.50      | sK5 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_6936]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_18,plain,
% 7.76/1.50      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.76/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_28,plain,
% 7.76/1.50      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25,plain,
% 7.76/1.50      ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_22,negated_conjecture,
% 7.76/1.50      ( sK5 != sK6 ),
% 7.76/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(contradiction,plain,
% 7.76/1.50      ( $false ),
% 7.76/1.50      inference(minisat,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_27866,c_27754,c_26400,c_26386,c_24996,c_24312,c_14177,
% 7.76/1.50                 c_9122,c_8314,c_7194,c_6937,c_893,c_890,c_28,c_25,c_20,
% 7.76/1.50                 c_21,c_22,c_23]) ).
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  ------                               Statistics
% 7.76/1.50  
% 7.76/1.50  ------ Selected
% 7.76/1.50  
% 7.76/1.50  total_time:                             0.951
% 7.76/1.50  
%------------------------------------------------------------------------------
