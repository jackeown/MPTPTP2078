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
% DateTime   : Thu Dec  3 11:41:35 EST 2020

% Result     : Theorem 15.46s
% Output     : CNFRefutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 162 expanded)
%              Number of clauses        :   34 (  35 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  404 ( 569 expanded)
%              Number of equality atoms :  191 ( 292 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f45])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f113,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f17])).

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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f64,f83])).

fof(f104,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f105,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f104])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f85])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f96])).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK6)) != sK6 ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    k1_setfam_1(k1_tarski(sK6)) != sK6 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f47])).

fof(f82,plain,(
    k1_setfam_1(k1_tarski(sK6)) != sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != sK6 ),
    inference(definition_unfolding,[],[f82,f85])).

cnf(c_27,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK5(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1117,plain,
    ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1)))
    | sK5(k3_enumset1(X1,X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_27,c_23])).

cnf(c_369,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_52756,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK5(k3_enumset1(X1,X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_1117,c_369])).

cnf(c_52766,plain,
    ( r1_tarski(sK6,sK5(k3_enumset1(sK6,sK6,sK6,sK6,sK6),sK6))
    | r1_tarski(sK6,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
    | ~ r1_tarski(sK6,sK6)
    | sK6 != sK6
    | k1_xboole_0 = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_52756])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1036,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k3_enumset1(X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_11243,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k3_enumset1(X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_11247,plain,
    ( ~ r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK6,k1_xboole_0)
    | sK6 != sK6
    | k1_xboole_0 != k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_11243])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,sK5(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6942,plain,
    ( ~ r1_tarski(X0,sK5(k3_enumset1(sK6,sK6,sK6,sK6,sK6),X0))
    | r1_tarski(X0,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
    | k1_xboole_0 = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_6944,plain,
    ( ~ r1_tarski(sK6,sK5(k3_enumset1(sK6,sK6,sK6,sK6,sK6),sK6))
    | r1_tarski(sK6,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
    | k1_xboole_0 = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_6942])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_774,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_784,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1490,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_784])).

cnf(c_1727,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_1490])).

cnf(c_1741,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1727])).

cnf(c_1743,plain,
    ( ~ r2_hidden(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1014,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k3_enumset1(X2,X2,X2,X3,X0)),X1)
    | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X3,X0)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1016,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK6)
    | ~ r1_tarski(sK6,sK6)
    | ~ r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_996,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK6)
    | ~ r1_tarski(sK6,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
    | k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_71,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_49,plain,
    ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_29,negated_conjecture,
    ( k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != sK6 ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52766,c_11247,c_6944,c_1743,c_1016,c_996,c_71,c_49,c_46,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.46/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.46/2.48  
% 15.46/2.48  ------  iProver source info
% 15.46/2.48  
% 15.46/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.46/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.46/2.48  git: non_committed_changes: false
% 15.46/2.48  git: last_make_outside_of_git: false
% 15.46/2.48  
% 15.46/2.48  ------ 
% 15.46/2.48  
% 15.46/2.48  ------ Input Options
% 15.46/2.48  
% 15.46/2.48  --out_options                           all
% 15.46/2.48  --tptp_safe_out                         true
% 15.46/2.48  --problem_path                          ""
% 15.46/2.48  --include_path                          ""
% 15.46/2.48  --clausifier                            res/vclausify_rel
% 15.46/2.48  --clausifier_options                    --mode clausify
% 15.46/2.48  --stdin                                 false
% 15.46/2.48  --stats_out                             sel
% 15.46/2.48  
% 15.46/2.48  ------ General Options
% 15.46/2.48  
% 15.46/2.48  --fof                                   false
% 15.46/2.48  --time_out_real                         604.99
% 15.46/2.48  --time_out_virtual                      -1.
% 15.46/2.48  --symbol_type_check                     false
% 15.46/2.48  --clausify_out                          false
% 15.46/2.48  --sig_cnt_out                           false
% 15.46/2.48  --trig_cnt_out                          false
% 15.46/2.48  --trig_cnt_out_tolerance                1.
% 15.46/2.48  --trig_cnt_out_sk_spl                   false
% 15.46/2.48  --abstr_cl_out                          false
% 15.46/2.48  
% 15.46/2.48  ------ Global Options
% 15.46/2.48  
% 15.46/2.48  --schedule                              none
% 15.46/2.48  --add_important_lit                     false
% 15.46/2.48  --prop_solver_per_cl                    1000
% 15.46/2.48  --min_unsat_core                        false
% 15.46/2.48  --soft_assumptions                      false
% 15.46/2.48  --soft_lemma_size                       3
% 15.46/2.48  --prop_impl_unit_size                   0
% 15.46/2.48  --prop_impl_unit                        []
% 15.46/2.48  --share_sel_clauses                     true
% 15.46/2.48  --reset_solvers                         false
% 15.46/2.48  --bc_imp_inh                            [conj_cone]
% 15.46/2.48  --conj_cone_tolerance                   3.
% 15.46/2.48  --extra_neg_conj                        none
% 15.46/2.48  --large_theory_mode                     true
% 15.46/2.48  --prolific_symb_bound                   200
% 15.46/2.48  --lt_threshold                          2000
% 15.46/2.48  --clause_weak_htbl                      true
% 15.46/2.48  --gc_record_bc_elim                     false
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing Options
% 15.46/2.48  
% 15.46/2.48  --preprocessing_flag                    true
% 15.46/2.48  --time_out_prep_mult                    0.1
% 15.46/2.48  --splitting_mode                        input
% 15.46/2.48  --splitting_grd                         true
% 15.46/2.48  --splitting_cvd                         false
% 15.46/2.48  --splitting_cvd_svl                     false
% 15.46/2.48  --splitting_nvd                         32
% 15.46/2.48  --sub_typing                            true
% 15.46/2.48  --prep_gs_sim                           false
% 15.46/2.48  --prep_unflatten                        true
% 15.46/2.48  --prep_res_sim                          true
% 15.46/2.48  --prep_upred                            true
% 15.46/2.48  --prep_sem_filter                       exhaustive
% 15.46/2.48  --prep_sem_filter_out                   false
% 15.46/2.48  --pred_elim                             false
% 15.46/2.48  --res_sim_input                         true
% 15.46/2.48  --eq_ax_congr_red                       true
% 15.46/2.48  --pure_diseq_elim                       true
% 15.46/2.48  --brand_transform                       false
% 15.46/2.48  --non_eq_to_eq                          false
% 15.46/2.48  --prep_def_merge                        true
% 15.46/2.48  --prep_def_merge_prop_impl              false
% 15.46/2.48  --prep_def_merge_mbd                    true
% 15.46/2.48  --prep_def_merge_tr_red                 false
% 15.46/2.48  --prep_def_merge_tr_cl                  false
% 15.46/2.48  --smt_preprocessing                     true
% 15.46/2.48  --smt_ac_axioms                         fast
% 15.46/2.48  --preprocessed_out                      false
% 15.46/2.48  --preprocessed_stats                    false
% 15.46/2.48  
% 15.46/2.48  ------ Abstraction refinement Options
% 15.46/2.48  
% 15.46/2.48  --abstr_ref                             []
% 15.46/2.48  --abstr_ref_prep                        false
% 15.46/2.48  --abstr_ref_until_sat                   false
% 15.46/2.48  --abstr_ref_sig_restrict                funpre
% 15.46/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.46/2.48  --abstr_ref_under                       []
% 15.46/2.48  
% 15.46/2.48  ------ SAT Options
% 15.46/2.48  
% 15.46/2.48  --sat_mode                              false
% 15.46/2.48  --sat_fm_restart_options                ""
% 15.46/2.48  --sat_gr_def                            false
% 15.46/2.48  --sat_epr_types                         true
% 15.46/2.48  --sat_non_cyclic_types                  false
% 15.46/2.48  --sat_finite_models                     false
% 15.46/2.48  --sat_fm_lemmas                         false
% 15.46/2.48  --sat_fm_prep                           false
% 15.46/2.48  --sat_fm_uc_incr                        true
% 15.46/2.48  --sat_out_model                         small
% 15.46/2.48  --sat_out_clauses                       false
% 15.46/2.48  
% 15.46/2.48  ------ QBF Options
% 15.46/2.48  
% 15.46/2.48  --qbf_mode                              false
% 15.46/2.48  --qbf_elim_univ                         false
% 15.46/2.48  --qbf_dom_inst                          none
% 15.46/2.48  --qbf_dom_pre_inst                      false
% 15.46/2.48  --qbf_sk_in                             false
% 15.46/2.48  --qbf_pred_elim                         true
% 15.46/2.48  --qbf_split                             512
% 15.46/2.48  
% 15.46/2.48  ------ BMC1 Options
% 15.46/2.48  
% 15.46/2.48  --bmc1_incremental                      false
% 15.46/2.48  --bmc1_axioms                           reachable_all
% 15.46/2.48  --bmc1_min_bound                        0
% 15.46/2.48  --bmc1_max_bound                        -1
% 15.46/2.48  --bmc1_max_bound_default                -1
% 15.46/2.48  --bmc1_symbol_reachability              true
% 15.46/2.48  --bmc1_property_lemmas                  false
% 15.46/2.48  --bmc1_k_induction                      false
% 15.46/2.48  --bmc1_non_equiv_states                 false
% 15.46/2.48  --bmc1_deadlock                         false
% 15.46/2.48  --bmc1_ucm                              false
% 15.46/2.48  --bmc1_add_unsat_core                   none
% 15.46/2.48  --bmc1_unsat_core_children              false
% 15.46/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.46/2.48  --bmc1_out_stat                         full
% 15.46/2.48  --bmc1_ground_init                      false
% 15.46/2.48  --bmc1_pre_inst_next_state              false
% 15.46/2.48  --bmc1_pre_inst_state                   false
% 15.46/2.48  --bmc1_pre_inst_reach_state             false
% 15.46/2.48  --bmc1_out_unsat_core                   false
% 15.46/2.48  --bmc1_aig_witness_out                  false
% 15.46/2.48  --bmc1_verbose                          false
% 15.46/2.48  --bmc1_dump_clauses_tptp                false
% 15.46/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.46/2.48  --bmc1_dump_file                        -
% 15.46/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.46/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.46/2.48  --bmc1_ucm_extend_mode                  1
% 15.46/2.48  --bmc1_ucm_init_mode                    2
% 15.46/2.48  --bmc1_ucm_cone_mode                    none
% 15.46/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.46/2.48  --bmc1_ucm_relax_model                  4
% 15.46/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.46/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.46/2.48  --bmc1_ucm_layered_model                none
% 15.46/2.48  --bmc1_ucm_max_lemma_size               10
% 15.46/2.48  
% 15.46/2.48  ------ AIG Options
% 15.46/2.48  
% 15.46/2.48  --aig_mode                              false
% 15.46/2.48  
% 15.46/2.48  ------ Instantiation Options
% 15.46/2.48  
% 15.46/2.48  --instantiation_flag                    true
% 15.46/2.48  --inst_sos_flag                         false
% 15.46/2.48  --inst_sos_phase                        true
% 15.46/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.46/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.46/2.48  --inst_lit_sel_side                     num_symb
% 15.46/2.48  --inst_solver_per_active                1400
% 15.46/2.48  --inst_solver_calls_frac                1.
% 15.46/2.48  --inst_passive_queue_type               priority_queues
% 15.46/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.46/2.48  --inst_passive_queues_freq              [25;2]
% 15.46/2.48  --inst_dismatching                      true
% 15.46/2.48  --inst_eager_unprocessed_to_passive     true
% 15.46/2.48  --inst_prop_sim_given                   true
% 15.46/2.48  --inst_prop_sim_new                     false
% 15.46/2.48  --inst_subs_new                         false
% 15.46/2.48  --inst_eq_res_simp                      false
% 15.46/2.48  --inst_subs_given                       false
% 15.46/2.48  --inst_orphan_elimination               true
% 15.46/2.48  --inst_learning_loop_flag               true
% 15.46/2.48  --inst_learning_start                   3000
% 15.46/2.48  --inst_learning_factor                  2
% 15.46/2.48  --inst_start_prop_sim_after_learn       3
% 15.46/2.48  --inst_sel_renew                        solver
% 15.46/2.48  --inst_lit_activity_flag                true
% 15.46/2.48  --inst_restr_to_given                   false
% 15.46/2.48  --inst_activity_threshold               500
% 15.46/2.48  --inst_out_proof                        true
% 15.46/2.48  
% 15.46/2.48  ------ Resolution Options
% 15.46/2.48  
% 15.46/2.48  --resolution_flag                       true
% 15.46/2.48  --res_lit_sel                           adaptive
% 15.46/2.48  --res_lit_sel_side                      none
% 15.46/2.48  --res_ordering                          kbo
% 15.46/2.48  --res_to_prop_solver                    active
% 15.46/2.48  --res_prop_simpl_new                    false
% 15.46/2.48  --res_prop_simpl_given                  true
% 15.46/2.48  --res_passive_queue_type                priority_queues
% 15.46/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.46/2.48  --res_passive_queues_freq               [15;5]
% 15.46/2.48  --res_forward_subs                      full
% 15.46/2.48  --res_backward_subs                     full
% 15.46/2.48  --res_forward_subs_resolution           true
% 15.46/2.48  --res_backward_subs_resolution          true
% 15.46/2.48  --res_orphan_elimination                true
% 15.46/2.48  --res_time_limit                        2.
% 15.46/2.48  --res_out_proof                         true
% 15.46/2.48  
% 15.46/2.48  ------ Superposition Options
% 15.46/2.48  
% 15.46/2.48  --superposition_flag                    true
% 15.46/2.48  --sup_passive_queue_type                priority_queues
% 15.46/2.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.46/2.48  --sup_passive_queues_freq               [1;4]
% 15.46/2.48  --demod_completeness_check              fast
% 15.46/2.48  --demod_use_ground                      true
% 15.46/2.48  --sup_to_prop_solver                    passive
% 15.46/2.48  --sup_prop_simpl_new                    true
% 15.46/2.48  --sup_prop_simpl_given                  true
% 15.46/2.48  --sup_fun_splitting                     false
% 15.46/2.48  --sup_smt_interval                      50000
% 15.46/2.48  
% 15.46/2.48  ------ Superposition Simplification Setup
% 15.46/2.48  
% 15.46/2.48  --sup_indices_passive                   []
% 15.46/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.46/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.46/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.46/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.46/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.46/2.48  --sup_full_bw                           [BwDemod]
% 15.46/2.48  --sup_immed_triv                        [TrivRules]
% 15.46/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.46/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.46/2.48  --sup_immed_bw_main                     []
% 15.46/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.46/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.46/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.46/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.46/2.48  
% 15.46/2.48  ------ Combination Options
% 15.46/2.48  
% 15.46/2.48  --comb_res_mult                         3
% 15.46/2.48  --comb_sup_mult                         2
% 15.46/2.48  --comb_inst_mult                        10
% 15.46/2.48  
% 15.46/2.48  ------ Debug Options
% 15.46/2.48  
% 15.46/2.48  --dbg_backtrace                         false
% 15.46/2.48  --dbg_dump_prop_clauses                 false
% 15.46/2.48  --dbg_dump_prop_clauses_file            -
% 15.46/2.48  --dbg_out_stat                          false
% 15.46/2.48  ------ Parsing...
% 15.46/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  ------ Proving...
% 15.46/2.48  ------ Problem Properties 
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  clauses                                 29
% 15.46/2.48  conjectures                             1
% 15.46/2.48  EPR                                     2
% 15.46/2.48  Horn                                    19
% 15.46/2.48  unary                                   7
% 15.46/2.48  binary                                  4
% 15.46/2.48  lits                                    73
% 15.46/2.48  lits eq                                 28
% 15.46/2.48  fd_pure                                 0
% 15.46/2.48  fd_pseudo                               0
% 15.46/2.48  fd_cond                                 2
% 15.46/2.48  fd_pseudo_cond                          12
% 15.46/2.48  AC symbols                              0
% 15.46/2.48  
% 15.46/2.48  ------ Input Options Time Limit: Unbounded
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ 
% 15.46/2.48  Current options:
% 15.46/2.48  ------ 
% 15.46/2.48  
% 15.46/2.48  ------ Input Options
% 15.46/2.48  
% 15.46/2.48  --out_options                           all
% 15.46/2.48  --tptp_safe_out                         true
% 15.46/2.48  --problem_path                          ""
% 15.46/2.48  --include_path                          ""
% 15.46/2.48  --clausifier                            res/vclausify_rel
% 15.46/2.48  --clausifier_options                    --mode clausify
% 15.46/2.48  --stdin                                 false
% 15.46/2.48  --stats_out                             sel
% 15.46/2.48  
% 15.46/2.48  ------ General Options
% 15.46/2.48  
% 15.46/2.48  --fof                                   false
% 15.46/2.48  --time_out_real                         604.99
% 15.46/2.48  --time_out_virtual                      -1.
% 15.46/2.48  --symbol_type_check                     false
% 15.46/2.48  --clausify_out                          false
% 15.46/2.48  --sig_cnt_out                           false
% 15.46/2.48  --trig_cnt_out                          false
% 15.46/2.48  --trig_cnt_out_tolerance                1.
% 15.46/2.48  --trig_cnt_out_sk_spl                   false
% 15.46/2.48  --abstr_cl_out                          false
% 15.46/2.48  
% 15.46/2.48  ------ Global Options
% 15.46/2.48  
% 15.46/2.48  --schedule                              none
% 15.46/2.48  --add_important_lit                     false
% 15.46/2.48  --prop_solver_per_cl                    1000
% 15.46/2.48  --min_unsat_core                        false
% 15.46/2.48  --soft_assumptions                      false
% 15.46/2.48  --soft_lemma_size                       3
% 15.46/2.48  --prop_impl_unit_size                   0
% 15.46/2.48  --prop_impl_unit                        []
% 15.46/2.48  --share_sel_clauses                     true
% 15.46/2.48  --reset_solvers                         false
% 15.46/2.48  --bc_imp_inh                            [conj_cone]
% 15.46/2.48  --conj_cone_tolerance                   3.
% 15.46/2.48  --extra_neg_conj                        none
% 15.46/2.48  --large_theory_mode                     true
% 15.46/2.48  --prolific_symb_bound                   200
% 15.46/2.48  --lt_threshold                          2000
% 15.46/2.48  --clause_weak_htbl                      true
% 15.46/2.48  --gc_record_bc_elim                     false
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing Options
% 15.46/2.48  
% 15.46/2.48  --preprocessing_flag                    true
% 15.46/2.48  --time_out_prep_mult                    0.1
% 15.46/2.48  --splitting_mode                        input
% 15.46/2.48  --splitting_grd                         true
% 15.46/2.48  --splitting_cvd                         false
% 15.46/2.48  --splitting_cvd_svl                     false
% 15.46/2.48  --splitting_nvd                         32
% 15.46/2.48  --sub_typing                            true
% 15.46/2.48  --prep_gs_sim                           false
% 15.46/2.48  --prep_unflatten                        true
% 15.46/2.48  --prep_res_sim                          true
% 15.46/2.48  --prep_upred                            true
% 15.46/2.48  --prep_sem_filter                       exhaustive
% 15.46/2.48  --prep_sem_filter_out                   false
% 15.46/2.48  --pred_elim                             false
% 15.46/2.48  --res_sim_input                         true
% 15.46/2.48  --eq_ax_congr_red                       true
% 15.46/2.48  --pure_diseq_elim                       true
% 15.46/2.48  --brand_transform                       false
% 15.46/2.48  --non_eq_to_eq                          false
% 15.46/2.48  --prep_def_merge                        true
% 15.46/2.48  --prep_def_merge_prop_impl              false
% 15.46/2.48  --prep_def_merge_mbd                    true
% 15.46/2.48  --prep_def_merge_tr_red                 false
% 15.46/2.48  --prep_def_merge_tr_cl                  false
% 15.46/2.48  --smt_preprocessing                     true
% 15.46/2.48  --smt_ac_axioms                         fast
% 15.46/2.48  --preprocessed_out                      false
% 15.46/2.48  --preprocessed_stats                    false
% 15.46/2.48  
% 15.46/2.48  ------ Abstraction refinement Options
% 15.46/2.48  
% 15.46/2.48  --abstr_ref                             []
% 15.46/2.48  --abstr_ref_prep                        false
% 15.46/2.48  --abstr_ref_until_sat                   false
% 15.46/2.48  --abstr_ref_sig_restrict                funpre
% 15.46/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.46/2.48  --abstr_ref_under                       []
% 15.46/2.48  
% 15.46/2.48  ------ SAT Options
% 15.46/2.48  
% 15.46/2.48  --sat_mode                              false
% 15.46/2.48  --sat_fm_restart_options                ""
% 15.46/2.48  --sat_gr_def                            false
% 15.46/2.48  --sat_epr_types                         true
% 15.46/2.48  --sat_non_cyclic_types                  false
% 15.46/2.48  --sat_finite_models                     false
% 15.46/2.48  --sat_fm_lemmas                         false
% 15.46/2.48  --sat_fm_prep                           false
% 15.46/2.48  --sat_fm_uc_incr                        true
% 15.46/2.48  --sat_out_model                         small
% 15.46/2.48  --sat_out_clauses                       false
% 15.46/2.48  
% 15.46/2.48  ------ QBF Options
% 15.46/2.48  
% 15.46/2.48  --qbf_mode                              false
% 15.46/2.48  --qbf_elim_univ                         false
% 15.46/2.48  --qbf_dom_inst                          none
% 15.46/2.48  --qbf_dom_pre_inst                      false
% 15.46/2.48  --qbf_sk_in                             false
% 15.46/2.48  --qbf_pred_elim                         true
% 15.46/2.48  --qbf_split                             512
% 15.46/2.48  
% 15.46/2.48  ------ BMC1 Options
% 15.46/2.48  
% 15.46/2.48  --bmc1_incremental                      false
% 15.46/2.48  --bmc1_axioms                           reachable_all
% 15.46/2.48  --bmc1_min_bound                        0
% 15.46/2.48  --bmc1_max_bound                        -1
% 15.46/2.48  --bmc1_max_bound_default                -1
% 15.46/2.48  --bmc1_symbol_reachability              true
% 15.46/2.48  --bmc1_property_lemmas                  false
% 15.46/2.48  --bmc1_k_induction                      false
% 15.46/2.48  --bmc1_non_equiv_states                 false
% 15.46/2.48  --bmc1_deadlock                         false
% 15.46/2.48  --bmc1_ucm                              false
% 15.46/2.48  --bmc1_add_unsat_core                   none
% 15.46/2.48  --bmc1_unsat_core_children              false
% 15.46/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.46/2.48  --bmc1_out_stat                         full
% 15.46/2.48  --bmc1_ground_init                      false
% 15.46/2.48  --bmc1_pre_inst_next_state              false
% 15.46/2.48  --bmc1_pre_inst_state                   false
% 15.46/2.48  --bmc1_pre_inst_reach_state             false
% 15.46/2.48  --bmc1_out_unsat_core                   false
% 15.46/2.48  --bmc1_aig_witness_out                  false
% 15.46/2.48  --bmc1_verbose                          false
% 15.46/2.48  --bmc1_dump_clauses_tptp                false
% 15.46/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.46/2.48  --bmc1_dump_file                        -
% 15.46/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.46/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.46/2.48  --bmc1_ucm_extend_mode                  1
% 15.46/2.48  --bmc1_ucm_init_mode                    2
% 15.46/2.48  --bmc1_ucm_cone_mode                    none
% 15.46/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.46/2.48  --bmc1_ucm_relax_model                  4
% 15.46/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.46/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.46/2.48  --bmc1_ucm_layered_model                none
% 15.46/2.48  --bmc1_ucm_max_lemma_size               10
% 15.46/2.48  
% 15.46/2.48  ------ AIG Options
% 15.46/2.48  
% 15.46/2.48  --aig_mode                              false
% 15.46/2.48  
% 15.46/2.48  ------ Instantiation Options
% 15.46/2.48  
% 15.46/2.48  --instantiation_flag                    true
% 15.46/2.48  --inst_sos_flag                         false
% 15.46/2.48  --inst_sos_phase                        true
% 15.46/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.46/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.46/2.48  --inst_lit_sel_side                     num_symb
% 15.46/2.48  --inst_solver_per_active                1400
% 15.46/2.48  --inst_solver_calls_frac                1.
% 15.46/2.48  --inst_passive_queue_type               priority_queues
% 15.46/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.46/2.48  --inst_passive_queues_freq              [25;2]
% 15.46/2.48  --inst_dismatching                      true
% 15.46/2.48  --inst_eager_unprocessed_to_passive     true
% 15.46/2.48  --inst_prop_sim_given                   true
% 15.46/2.48  --inst_prop_sim_new                     false
% 15.46/2.48  --inst_subs_new                         false
% 15.46/2.48  --inst_eq_res_simp                      false
% 15.46/2.48  --inst_subs_given                       false
% 15.46/2.48  --inst_orphan_elimination               true
% 15.46/2.48  --inst_learning_loop_flag               true
% 15.46/2.48  --inst_learning_start                   3000
% 15.46/2.48  --inst_learning_factor                  2
% 15.46/2.48  --inst_start_prop_sim_after_learn       3
% 15.46/2.48  --inst_sel_renew                        solver
% 15.46/2.48  --inst_lit_activity_flag                true
% 15.46/2.48  --inst_restr_to_given                   false
% 15.46/2.48  --inst_activity_threshold               500
% 15.46/2.48  --inst_out_proof                        true
% 15.46/2.48  
% 15.46/2.48  ------ Resolution Options
% 15.46/2.48  
% 15.46/2.48  --resolution_flag                       true
% 15.46/2.48  --res_lit_sel                           adaptive
% 15.46/2.48  --res_lit_sel_side                      none
% 15.46/2.48  --res_ordering                          kbo
% 15.46/2.48  --res_to_prop_solver                    active
% 15.46/2.48  --res_prop_simpl_new                    false
% 15.46/2.48  --res_prop_simpl_given                  true
% 15.46/2.48  --res_passive_queue_type                priority_queues
% 15.46/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.46/2.48  --res_passive_queues_freq               [15;5]
% 15.46/2.48  --res_forward_subs                      full
% 15.46/2.48  --res_backward_subs                     full
% 15.46/2.48  --res_forward_subs_resolution           true
% 15.46/2.48  --res_backward_subs_resolution          true
% 15.46/2.48  --res_orphan_elimination                true
% 15.46/2.48  --res_time_limit                        2.
% 15.46/2.48  --res_out_proof                         true
% 15.46/2.48  
% 15.46/2.48  ------ Superposition Options
% 15.46/2.48  
% 15.46/2.48  --superposition_flag                    true
% 15.46/2.48  --sup_passive_queue_type                priority_queues
% 15.46/2.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.46/2.48  --sup_passive_queues_freq               [1;4]
% 15.46/2.48  --demod_completeness_check              fast
% 15.46/2.48  --demod_use_ground                      true
% 15.46/2.48  --sup_to_prop_solver                    passive
% 15.46/2.48  --sup_prop_simpl_new                    true
% 15.46/2.48  --sup_prop_simpl_given                  true
% 15.46/2.48  --sup_fun_splitting                     false
% 15.46/2.48  --sup_smt_interval                      50000
% 15.46/2.48  
% 15.46/2.48  ------ Superposition Simplification Setup
% 15.46/2.48  
% 15.46/2.48  --sup_indices_passive                   []
% 15.46/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.46/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.46/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.46/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.46/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.46/2.48  --sup_full_bw                           [BwDemod]
% 15.46/2.48  --sup_immed_triv                        [TrivRules]
% 15.46/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.46/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.46/2.48  --sup_immed_bw_main                     []
% 15.46/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.46/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.46/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.46/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.46/2.48  
% 15.46/2.48  ------ Combination Options
% 15.46/2.48  
% 15.46/2.48  --comb_res_mult                         3
% 15.46/2.48  --comb_sup_mult                         2
% 15.46/2.48  --comb_inst_mult                        10
% 15.46/2.48  
% 15.46/2.48  ------ Debug Options
% 15.46/2.48  
% 15.46/2.48  --dbg_backtrace                         false
% 15.46/2.48  --dbg_dump_prop_clauses                 false
% 15.46/2.48  --dbg_dump_prop_clauses_file            -
% 15.46/2.48  --dbg_out_stat                          false
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  % SZS status Theorem for theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  fof(f12,axiom,(
% 15.46/2.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f19,plain,(
% 15.46/2.48    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 15.46/2.48    inference(ennf_transformation,[],[f12])).
% 15.46/2.48  
% 15.46/2.48  fof(f20,plain,(
% 15.46/2.48    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 15.46/2.48    inference(flattening,[],[f19])).
% 15.46/2.48  
% 15.46/2.48  fof(f45,plain,(
% 15.46/2.48    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f46,plain,(
% 15.46/2.48    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f45])).
% 15.46/2.48  
% 15.46/2.48  fof(f79,plain,(
% 15.46/2.48    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f46])).
% 15.46/2.48  
% 15.46/2.48  fof(f6,axiom,(
% 15.46/2.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f39,plain,(
% 15.46/2.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 15.46/2.48    inference(nnf_transformation,[],[f6])).
% 15.46/2.48  
% 15.46/2.48  fof(f40,plain,(
% 15.46/2.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.46/2.48    inference(rectify,[],[f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f41,plain,(
% 15.46/2.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f42,plain,(
% 15.46/2.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 15.46/2.48  
% 15.46/2.48  fof(f69,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 15.46/2.48    inference(cnf_transformation,[],[f42])).
% 15.46/2.48  
% 15.46/2.48  fof(f7,axiom,(
% 15.46/2.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f73,plain,(
% 15.46/2.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f7])).
% 15.46/2.48  
% 15.46/2.48  fof(f8,axiom,(
% 15.46/2.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f74,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f8])).
% 15.46/2.48  
% 15.46/2.48  fof(f9,axiom,(
% 15.46/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f75,plain,(
% 15.46/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f9])).
% 15.46/2.48  
% 15.46/2.48  fof(f10,axiom,(
% 15.46/2.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f76,plain,(
% 15.46/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f10])).
% 15.46/2.48  
% 15.46/2.48  fof(f83,plain,(
% 15.46/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.46/2.48    inference(definition_unfolding,[],[f75,f76])).
% 15.46/2.48  
% 15.46/2.48  fof(f84,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.46/2.48    inference(definition_unfolding,[],[f74,f83])).
% 15.46/2.48  
% 15.46/2.48  fof(f85,plain,(
% 15.46/2.48    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.46/2.48    inference(definition_unfolding,[],[f73,f84])).
% 15.46/2.48  
% 15.46/2.48  fof(f97,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 15.46/2.48    inference(definition_unfolding,[],[f69,f85])).
% 15.46/2.48  
% 15.46/2.48  fof(f113,plain,(
% 15.46/2.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 15.46/2.48    inference(equality_resolution,[],[f97])).
% 15.46/2.48  
% 15.46/2.48  fof(f80,plain,(
% 15.46/2.48    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK5(X0,X1))) )),
% 15.46/2.48    inference(cnf_transformation,[],[f46])).
% 15.46/2.48  
% 15.46/2.48  fof(f5,axiom,(
% 15.46/2.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f17,plain,(
% 15.46/2.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.46/2.48    inference(ennf_transformation,[],[f5])).
% 15.46/2.48  
% 15.46/2.48  fof(f34,plain,(
% 15.46/2.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.46/2.48    inference(nnf_transformation,[],[f17])).
% 15.46/2.48  
% 15.46/2.48  fof(f35,plain,(
% 15.46/2.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.46/2.48    inference(flattening,[],[f34])).
% 15.46/2.48  
% 15.46/2.48  fof(f36,plain,(
% 15.46/2.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.46/2.48    inference(rectify,[],[f35])).
% 15.46/2.48  
% 15.46/2.48  fof(f37,plain,(
% 15.46/2.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f38,plain,(
% 15.46/2.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 15.46/2.48  
% 15.46/2.48  fof(f64,plain,(
% 15.46/2.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.46/2.48    inference(cnf_transformation,[],[f38])).
% 15.46/2.48  
% 15.46/2.48  fof(f90,plain,(
% 15.46/2.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 15.46/2.48    inference(definition_unfolding,[],[f64,f83])).
% 15.46/2.48  
% 15.46/2.48  fof(f104,plain,(
% 15.46/2.48    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 15.46/2.48    inference(equality_resolution,[],[f90])).
% 15.46/2.48  
% 15.46/2.48  fof(f105,plain,(
% 15.46/2.48    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 15.46/2.48    inference(equality_resolution,[],[f104])).
% 15.46/2.48  
% 15.46/2.48  fof(f4,axiom,(
% 15.46/2.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f60,plain,(
% 15.46/2.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.46/2.48    inference(cnf_transformation,[],[f4])).
% 15.46/2.48  
% 15.46/2.48  fof(f1,axiom,(
% 15.46/2.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f24,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.46/2.48    inference(nnf_transformation,[],[f1])).
% 15.46/2.48  
% 15.46/2.48  fof(f25,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.46/2.48    inference(flattening,[],[f24])).
% 15.46/2.48  
% 15.46/2.48  fof(f26,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.46/2.48    inference(rectify,[],[f25])).
% 15.46/2.48  
% 15.46/2.48  fof(f27,plain,(
% 15.46/2.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f28,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 15.46/2.48  
% 15.46/2.48  fof(f50,plain,(
% 15.46/2.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.46/2.48    inference(cnf_transformation,[],[f28])).
% 15.46/2.48  
% 15.46/2.48  fof(f100,plain,(
% 15.46/2.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 15.46/2.48    inference(equality_resolution,[],[f50])).
% 15.46/2.48  
% 15.46/2.48  fof(f13,axiom,(
% 15.46/2.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f21,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 15.46/2.48    inference(ennf_transformation,[],[f13])).
% 15.46/2.48  
% 15.46/2.48  fof(f22,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 15.46/2.48    inference(flattening,[],[f21])).
% 15.46/2.48  
% 15.46/2.48  fof(f81,plain,(
% 15.46/2.48    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f22])).
% 15.46/2.48  
% 15.46/2.48  fof(f3,axiom,(
% 15.46/2.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f32,plain,(
% 15.46/2.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.46/2.48    inference(nnf_transformation,[],[f3])).
% 15.46/2.48  
% 15.46/2.48  fof(f33,plain,(
% 15.46/2.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.46/2.48    inference(flattening,[],[f32])).
% 15.46/2.48  
% 15.46/2.48  fof(f59,plain,(
% 15.46/2.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f33])).
% 15.46/2.48  
% 15.46/2.48  fof(f57,plain,(
% 15.46/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.46/2.48    inference(cnf_transformation,[],[f33])).
% 15.46/2.48  
% 15.46/2.48  fof(f103,plain,(
% 15.46/2.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.46/2.48    inference(equality_resolution,[],[f57])).
% 15.46/2.48  
% 15.46/2.48  fof(f70,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 15.46/2.48    inference(cnf_transformation,[],[f42])).
% 15.46/2.48  
% 15.46/2.48  fof(f96,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 15.46/2.48    inference(definition_unfolding,[],[f70,f85])).
% 15.46/2.48  
% 15.46/2.48  fof(f111,plain,(
% 15.46/2.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 15.46/2.48    inference(equality_resolution,[],[f96])).
% 15.46/2.48  
% 15.46/2.48  fof(f112,plain,(
% 15.46/2.48    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 15.46/2.48    inference(equality_resolution,[],[f111])).
% 15.46/2.48  
% 15.46/2.48  fof(f14,conjecture,(
% 15.46/2.48    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f15,negated_conjecture,(
% 15.46/2.48    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 15.46/2.48    inference(negated_conjecture,[],[f14])).
% 15.46/2.48  
% 15.46/2.48  fof(f23,plain,(
% 15.46/2.48    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 15.46/2.48    inference(ennf_transformation,[],[f15])).
% 15.46/2.48  
% 15.46/2.48  fof(f47,plain,(
% 15.46/2.48    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK6)) != sK6),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f48,plain,(
% 15.46/2.48    k1_setfam_1(k1_tarski(sK6)) != sK6),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f47])).
% 15.46/2.48  
% 15.46/2.48  fof(f82,plain,(
% 15.46/2.48    k1_setfam_1(k1_tarski(sK6)) != sK6),
% 15.46/2.48    inference(cnf_transformation,[],[f48])).
% 15.46/2.48  
% 15.46/2.48  fof(f98,plain,(
% 15.46/2.48    k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != sK6),
% 15.46/2.48    inference(definition_unfolding,[],[f82,f85])).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27,plain,
% 15.46/2.48      ( r1_tarski(X0,k1_setfam_1(X1))
% 15.46/2.48      | r2_hidden(sK5(X1,X0),X1)
% 15.46/2.48      | k1_xboole_0 = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f79]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_23,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f113]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1117,plain,
% 15.46/2.48      ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1)))
% 15.46/2.48      | sK5(k3_enumset1(X1,X1,X1,X1,X1),X0) = X1
% 15.46/2.48      | k1_xboole_0 = k3_enumset1(X1,X1,X1,X1,X1) ),
% 15.46/2.48      inference(resolution,[status(thm)],[c_27,c_23]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_369,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.46/2.48      theory(equality) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_52756,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,X1)
% 15.46/2.48      | r1_tarski(X2,sK5(k3_enumset1(X1,X1,X1,X1,X1),X3))
% 15.46/2.48      | r1_tarski(X3,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1)))
% 15.46/2.48      | X2 != X0
% 15.46/2.48      | k1_xboole_0 = k3_enumset1(X1,X1,X1,X1,X1) ),
% 15.46/2.48      inference(resolution,[status(thm)],[c_1117,c_369]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_52766,plain,
% 15.46/2.48      ( r1_tarski(sK6,sK5(k3_enumset1(sK6,sK6,sK6,sK6,sK6),sK6))
% 15.46/2.48      | r1_tarski(sK6,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
% 15.46/2.48      | ~ r1_tarski(sK6,sK6)
% 15.46/2.48      | sK6 != sK6
% 15.46/2.48      | k1_xboole_0 = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_52756]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_368,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.46/2.48      theory(equality) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1036,plain,
% 15.46/2.48      ( r2_hidden(X0,X1)
% 15.46/2.48      | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X4,X2))
% 15.46/2.48      | X0 != X2
% 15.46/2.48      | X1 != k3_enumset1(X3,X3,X3,X4,X2) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_368]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_11243,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))
% 15.46/2.48      | r2_hidden(X3,k1_xboole_0)
% 15.46/2.48      | X3 != X0
% 15.46/2.48      | k1_xboole_0 != k3_enumset1(X1,X1,X1,X2,X0) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_1036]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_11247,plain,
% 15.46/2.48      ( ~ r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6))
% 15.46/2.48      | r2_hidden(sK6,k1_xboole_0)
% 15.46/2.48      | sK6 != sK6
% 15.46/2.48      | k1_xboole_0 != k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_11243]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_26,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,sK5(X1,X0))
% 15.46/2.48      | r1_tarski(X0,k1_setfam_1(X1))
% 15.46/2.48      | k1_xboole_0 = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f80]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_6942,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,sK5(k3_enumset1(sK6,sK6,sK6,sK6,sK6),X0))
% 15.46/2.48      | r1_tarski(X0,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
% 15.46/2.48      | k1_xboole_0 = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_26]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_6944,plain,
% 15.46/2.48      ( ~ r1_tarski(sK6,sK5(k3_enumset1(sK6,sK6,sK6,sK6,sK6),sK6))
% 15.46/2.48      | r1_tarski(sK6,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
% 15.46/2.48      | k1_xboole_0 = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_6942]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_16,plain,
% 15.46/2.48      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 15.46/2.48      inference(cnf_transformation,[],[f105]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_774,plain,
% 15.46/2.48      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_11,plain,
% 15.46/2.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.46/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_4,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 15.46/2.48      inference(cnf_transformation,[],[f100]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_784,plain,
% 15.46/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.46/2.48      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1490,plain,
% 15.46/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.46/2.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_11,c_784]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1727,plain,
% 15.46/2.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_774,c_1490]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1741,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 15.46/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_1727]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1743,plain,
% 15.46/2.48      ( ~ r2_hidden(sK6,k1_xboole_0) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_1741]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,X1)
% 15.46/2.48      | r1_tarski(k1_setfam_1(X2),X1)
% 15.46/2.48      | ~ r2_hidden(X0,X2) ),
% 15.46/2.48      inference(cnf_transformation,[],[f81]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1014,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,X1)
% 15.46/2.48      | r1_tarski(k1_setfam_1(k3_enumset1(X2,X2,X2,X3,X0)),X1)
% 15.46/2.48      | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X3,X0)) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_28]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1016,plain,
% 15.46/2.48      ( r1_tarski(k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK6)
% 15.46/2.48      | ~ r1_tarski(sK6,sK6)
% 15.46/2.48      | ~ r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_1014]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_8,plain,
% 15.46/2.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_996,plain,
% 15.46/2.48      ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK6)
% 15.46/2.48      | ~ r1_tarski(sK6,k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)))
% 15.46/2.48      | k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = sK6 ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_8]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_10,plain,
% 15.46/2.48      ( r1_tarski(X0,X0) ),
% 15.46/2.48      inference(cnf_transformation,[],[f103]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_71,plain,
% 15.46/2.48      ( r1_tarski(sK6,sK6) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_10]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_22,plain,
% 15.46/2.48      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 15.46/2.48      inference(cnf_transformation,[],[f112]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_49,plain,
% 15.46/2.48      ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_22]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_46,plain,
% 15.46/2.48      ( ~ r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) | sK6 = sK6 ),
% 15.46/2.48      inference(instantiation,[status(thm)],[c_23]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_29,negated_conjecture,
% 15.46/2.48      ( k1_setfam_1(k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != sK6 ),
% 15.46/2.48      inference(cnf_transformation,[],[f98]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(contradiction,plain,
% 15.46/2.48      ( $false ),
% 15.46/2.48      inference(minisat,
% 15.46/2.48                [status(thm)],
% 15.46/2.48                [c_52766,c_11247,c_6944,c_1743,c_1016,c_996,c_71,c_49,
% 15.46/2.48                 c_46,c_29]) ).
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  ------                               Statistics
% 15.46/2.48  
% 15.46/2.48  ------ Selected
% 15.46/2.48  
% 15.46/2.48  total_time:                             1.679
% 15.46/2.48  
%------------------------------------------------------------------------------
