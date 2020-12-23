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
% DateTime   : Thu Dec  3 11:41:34 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 184 expanded)
%              Number of clauses        :   45 (  59 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  419 ( 621 expanded)
%              Number of equality atoms :  204 ( 329 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f41])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f106,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f97,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f98,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f97])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f104,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f89])).

fof(f105,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f104])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f43])).

fof(f76,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f76,f78])).

cnf(c_351,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_993,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_35425,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | X0 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_35427,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_35425])).

cnf(c_26,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1062,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_26,c_24])).

cnf(c_350,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_349,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_348,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2186,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_349,c_348])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2197,plain,
    ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2186,c_12])).

cnf(c_2947,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k4_xboole_0(X1,k1_xboole_0))
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_350,c_2197])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_10633,plain,
    ( r1_tarski(X0,X1)
    | X0 != k4_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2947,c_11])).

cnf(c_2394,plain,
    ( X0 = X1
    | X1 != k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2197,c_349])).

cnf(c_2185,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_349,c_12])).

cnf(c_2610,plain,
    ( X0 = k4_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X0,k1_xboole_0) != X1 ),
    inference(resolution,[status(thm)],[c_2394,c_2185])).

cnf(c_5049,plain,
    ( X0 != X1
    | X1 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2610,c_2185])).

cnf(c_10905,plain,
    ( r1_tarski(X0,X1)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_10633,c_5049])).

cnf(c_23536,plain,
    ( r1_tarski(X0,sK4(k2_enumset1(X0,X0,X0,X0),X1))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
    | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ),
    inference(resolution,[status(thm)],[c_1062,c_10905])).

cnf(c_23538,plain,
    ( r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_23536])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,sK4(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5440,plain,
    ( ~ r1_tarski(X0,sK4(k2_enumset1(sK5,sK5,sK5,sK5),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_5442,plain,
    ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5440])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_744,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_752,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1426,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_752])).

cnf(c_1643,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_1426])).

cnf(c_1650,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1643])).

cnf(c_1652,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_972,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | ~ r1_tarski(X0,X3)
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_974,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_957,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_64,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_23,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_42,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_39,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_28,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35427,c_23538,c_5442,c_1652,c_974,c_957,c_64,c_42,c_39,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.68/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.68/2.00  
% 11.68/2.00  ------  iProver source info
% 11.68/2.00  
% 11.68/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.68/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.68/2.00  git: non_committed_changes: false
% 11.68/2.00  git: last_make_outside_of_git: false
% 11.68/2.00  
% 11.68/2.00  ------ 
% 11.68/2.00  ------ Parsing...
% 11.68/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.68/2.00  ------ Proving...
% 11.68/2.00  ------ Problem Properties 
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  clauses                                 28
% 11.68/2.00  conjectures                             1
% 11.68/2.00  EPR                                     3
% 11.68/2.00  Horn                                    18
% 11.68/2.00  unary                                   7
% 11.68/2.00  binary                                  5
% 11.68/2.00  lits                                    69
% 11.68/2.00  lits eq                                 26
% 11.68/2.00  fd_pure                                 0
% 11.68/2.00  fd_pseudo                               0
% 11.68/2.00  fd_cond                                 2
% 11.68/2.00  fd_pseudo_cond                          10
% 11.68/2.00  AC symbols                              0
% 11.68/2.00  
% 11.68/2.00  ------ Input Options Time Limit: Unbounded
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  ------ 
% 11.68/2.00  Current options:
% 11.68/2.00  ------ 
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  ------ Proving...
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  % SZS status Theorem for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  fof(f10,axiom,(
% 11.68/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f16,plain,(
% 11.68/2.00    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.68/2.00    inference(ennf_transformation,[],[f10])).
% 11.68/2.00  
% 11.68/2.00  fof(f17,plain,(
% 11.68/2.00    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.68/2.00    inference(flattening,[],[f16])).
% 11.68/2.00  
% 11.68/2.00  fof(f41,plain,(
% 11.68/2.00    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 11.68/2.00    introduced(choice_axiom,[])).
% 11.68/2.00  
% 11.68/2.00  fof(f42,plain,(
% 11.68/2.00    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 11.68/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f41])).
% 11.68/2.00  
% 11.68/2.00  fof(f73,plain,(
% 11.68/2.00    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f42])).
% 11.68/2.00  
% 11.68/2.00  fof(f6,axiom,(
% 11.68/2.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f37,plain,(
% 11.68/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.68/2.00    inference(nnf_transformation,[],[f6])).
% 11.68/2.00  
% 11.68/2.00  fof(f38,plain,(
% 11.68/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.68/2.00    inference(rectify,[],[f37])).
% 11.68/2.00  
% 11.68/2.00  fof(f39,plain,(
% 11.68/2.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 11.68/2.00    introduced(choice_axiom,[])).
% 11.68/2.00  
% 11.68/2.00  fof(f40,plain,(
% 11.68/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.68/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 11.68/2.00  
% 11.68/2.00  fof(f66,plain,(
% 11.68/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.68/2.00    inference(cnf_transformation,[],[f40])).
% 11.68/2.00  
% 11.68/2.00  fof(f7,axiom,(
% 11.68/2.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f70,plain,(
% 11.68/2.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f7])).
% 11.68/2.00  
% 11.68/2.00  fof(f8,axiom,(
% 11.68/2.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f71,plain,(
% 11.68/2.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f8])).
% 11.68/2.00  
% 11.68/2.00  fof(f9,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f72,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f9])).
% 11.68/2.00  
% 11.68/2.00  fof(f77,plain,(
% 11.68/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f71,f72])).
% 11.68/2.00  
% 11.68/2.00  fof(f78,plain,(
% 11.68/2.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f70,f77])).
% 11.68/2.00  
% 11.68/2.00  fof(f90,plain,(
% 11.68/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.68/2.00    inference(definition_unfolding,[],[f66,f78])).
% 11.68/2.00  
% 11.68/2.00  fof(f106,plain,(
% 11.68/2.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.68/2.00    inference(equality_resolution,[],[f90])).
% 11.68/2.00  
% 11.68/2.00  fof(f4,axiom,(
% 11.68/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f57,plain,(
% 11.68/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.68/2.00    inference(cnf_transformation,[],[f4])).
% 11.68/2.00  
% 11.68/2.00  fof(f3,axiom,(
% 11.68/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f30,plain,(
% 11.68/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.68/2.00    inference(nnf_transformation,[],[f3])).
% 11.68/2.00  
% 11.68/2.00  fof(f31,plain,(
% 11.68/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.68/2.00    inference(flattening,[],[f30])).
% 11.68/2.00  
% 11.68/2.00  fof(f54,plain,(
% 11.68/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.68/2.00    inference(cnf_transformation,[],[f31])).
% 11.68/2.00  
% 11.68/2.00  fof(f96,plain,(
% 11.68/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.68/2.00    inference(equality_resolution,[],[f54])).
% 11.68/2.00  
% 11.68/2.00  fof(f74,plain,(
% 11.68/2.00    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK4(X0,X1))) )),
% 11.68/2.00    inference(cnf_transformation,[],[f42])).
% 11.68/2.00  
% 11.68/2.00  fof(f5,axiom,(
% 11.68/2.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f15,plain,(
% 11.68/2.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.68/2.00    inference(ennf_transformation,[],[f5])).
% 11.68/2.00  
% 11.68/2.00  fof(f32,plain,(
% 11.68/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.68/2.00    inference(nnf_transformation,[],[f15])).
% 11.68/2.00  
% 11.68/2.00  fof(f33,plain,(
% 11.68/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.68/2.00    inference(flattening,[],[f32])).
% 11.68/2.00  
% 11.68/2.00  fof(f34,plain,(
% 11.68/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.68/2.00    inference(rectify,[],[f33])).
% 11.68/2.00  
% 11.68/2.00  fof(f35,plain,(
% 11.68/2.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 11.68/2.00    introduced(choice_axiom,[])).
% 11.68/2.00  
% 11.68/2.00  fof(f36,plain,(
% 11.68/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.68/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 11.68/2.00  
% 11.68/2.00  fof(f61,plain,(
% 11.68/2.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.68/2.00    inference(cnf_transformation,[],[f36])).
% 11.68/2.00  
% 11.68/2.00  fof(f83,plain,(
% 11.68/2.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.68/2.00    inference(definition_unfolding,[],[f61,f72])).
% 11.68/2.00  
% 11.68/2.00  fof(f97,plain,(
% 11.68/2.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 11.68/2.00    inference(equality_resolution,[],[f83])).
% 11.68/2.00  
% 11.68/2.00  fof(f98,plain,(
% 11.68/2.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 11.68/2.00    inference(equality_resolution,[],[f97])).
% 11.68/2.00  
% 11.68/2.00  fof(f2,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f25,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.68/2.00    inference(nnf_transformation,[],[f2])).
% 11.68/2.00  
% 11.68/2.00  fof(f26,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.68/2.00    inference(flattening,[],[f25])).
% 11.68/2.00  
% 11.68/2.00  fof(f27,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.68/2.00    inference(rectify,[],[f26])).
% 11.68/2.00  
% 11.68/2.00  fof(f28,plain,(
% 11.68/2.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.68/2.00    introduced(choice_axiom,[])).
% 11.68/2.00  
% 11.68/2.00  fof(f29,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.68/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 11.68/2.00  
% 11.68/2.00  fof(f49,plain,(
% 11.68/2.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.68/2.00    inference(cnf_transformation,[],[f29])).
% 11.68/2.00  
% 11.68/2.00  fof(f93,plain,(
% 11.68/2.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.68/2.00    inference(equality_resolution,[],[f49])).
% 11.68/2.00  
% 11.68/2.00  fof(f11,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f18,plain,(
% 11.68/2.00    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 11.68/2.00    inference(ennf_transformation,[],[f11])).
% 11.68/2.00  
% 11.68/2.00  fof(f19,plain,(
% 11.68/2.00    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 11.68/2.00    inference(flattening,[],[f18])).
% 11.68/2.00  
% 11.68/2.00  fof(f75,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f19])).
% 11.68/2.00  
% 11.68/2.00  fof(f56,plain,(
% 11.68/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f31])).
% 11.68/2.00  
% 11.68/2.00  fof(f67,plain,(
% 11.68/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.68/2.00    inference(cnf_transformation,[],[f40])).
% 11.68/2.00  
% 11.68/2.00  fof(f89,plain,(
% 11.68/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.68/2.00    inference(definition_unfolding,[],[f67,f78])).
% 11.68/2.00  
% 11.68/2.00  fof(f104,plain,(
% 11.68/2.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 11.68/2.00    inference(equality_resolution,[],[f89])).
% 11.68/2.00  
% 11.68/2.00  fof(f105,plain,(
% 11.68/2.00    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 11.68/2.00    inference(equality_resolution,[],[f104])).
% 11.68/2.00  
% 11.68/2.00  fof(f12,conjecture,(
% 11.68/2.00    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.68/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f13,negated_conjecture,(
% 11.68/2.00    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.68/2.00    inference(negated_conjecture,[],[f12])).
% 11.68/2.00  
% 11.68/2.00  fof(f20,plain,(
% 11.68/2.00    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 11.68/2.00    inference(ennf_transformation,[],[f13])).
% 11.68/2.00  
% 11.68/2.00  fof(f43,plain,(
% 11.68/2.00    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 11.68/2.00    introduced(choice_axiom,[])).
% 11.68/2.00  
% 11.68/2.00  fof(f44,plain,(
% 11.68/2.00    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 11.68/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f43])).
% 11.68/2.00  
% 11.68/2.00  fof(f76,plain,(
% 11.68/2.00    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 11.68/2.00    inference(cnf_transformation,[],[f44])).
% 11.68/2.00  
% 11.68/2.00  fof(f91,plain,(
% 11.68/2.00    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 11.68/2.00    inference(definition_unfolding,[],[f76,f78])).
% 11.68/2.00  
% 11.68/2.00  cnf(c_351,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.68/2.00      theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_993,plain,
% 11.68/2.00      ( r2_hidden(X0,X1)
% 11.68/2.00      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 11.68/2.00      | X0 != X2
% 11.68/2.00      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_351]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_35425,plain,
% 11.68/2.00      ( r2_hidden(X0,k1_xboole_0)
% 11.68/2.00      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 11.68/2.00      | X0 != sK5
% 11.68/2.00      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_993]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_35427,plain,
% 11.68/2.00      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 11.68/2.00      | r2_hidden(sK5,k1_xboole_0)
% 11.68/2.00      | sK5 != sK5
% 11.68/2.00      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_35425]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_26,plain,
% 11.68/2.00      ( r2_hidden(sK4(X0,X1),X0)
% 11.68/2.00      | r1_tarski(X1,k1_setfam_1(X0))
% 11.68/2.00      | k1_xboole_0 = X0 ),
% 11.68/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_24,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 11.68/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1062,plain,
% 11.68/2.00      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 11.68/2.00      | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 11.68/2.00      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_26,c_24]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_350,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.68/2.00      theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_349,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_348,plain,( X0 = X0 ),theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2186,plain,
% 11.68/2.00      ( X0 != X1 | X1 = X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_349,c_348]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_12,plain,
% 11.68/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.68/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2197,plain,
% 11.68/2.00      ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2186,c_12]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2947,plain,
% 11.68/2.00      ( r1_tarski(X0,X1)
% 11.68/2.00      | ~ r1_tarski(X2,k4_xboole_0(X1,k1_xboole_0))
% 11.68/2.00      | X0 != X2 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_350,c_2197]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_11,plain,
% 11.68/2.00      ( r1_tarski(X0,X0) ),
% 11.68/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_10633,plain,
% 11.68/2.00      ( r1_tarski(X0,X1) | X0 != k4_xboole_0(X1,k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2947,c_11]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2394,plain,
% 11.68/2.00      ( X0 = X1 | X1 != k4_xboole_0(X0,k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2197,c_349]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2185,plain,
% 11.68/2.00      ( X0 != X1 | k4_xboole_0(X1,k1_xboole_0) = X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_349,c_12]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2610,plain,
% 11.68/2.00      ( X0 = k4_xboole_0(X1,k1_xboole_0)
% 11.68/2.00      | k4_xboole_0(X0,k1_xboole_0) != X1 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2394,c_2185]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5049,plain,
% 11.68/2.00      ( X0 != X1 | X1 = k4_xboole_0(X0,k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2610,c_2185]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_10905,plain,
% 11.68/2.00      ( r1_tarski(X0,X1) | X1 != X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_10633,c_5049]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_23536,plain,
% 11.68/2.00      ( r1_tarski(X0,sK4(k2_enumset1(X0,X0,X0,X0),X1))
% 11.68/2.00      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
% 11.68/2.00      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_1062,c_10905]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_23538,plain,
% 11.68/2.00      ( r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 11.68/2.00      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.68/2.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_23536]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_25,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,sK4(X1,X0))
% 11.68/2.00      | r1_tarski(X0,k1_setfam_1(X1))
% 11.68/2.00      | k1_xboole_0 = X1 ),
% 11.68/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5440,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,sK4(k2_enumset1(sK5,sK5,sK5,sK5),X0))
% 11.68/2.00      | r1_tarski(X0,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.68/2.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5442,plain,
% 11.68/2.00      ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 11.68/2.00      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.68/2.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_5440]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_17,plain,
% 11.68/2.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 11.68/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_744,plain,
% 11.68/2.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 11.68/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_7,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 11.68/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_752,plain,
% 11.68/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.68/2.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.68/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1426,plain,
% 11.68/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.68/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.68/2.00      inference(superposition,[status(thm)],[c_12,c_752]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1643,plain,
% 11.68/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.68/2.00      inference(superposition,[status(thm)],[c_744,c_1426]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1650,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.68/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_1643]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1652,plain,
% 11.68/2.00      ( ~ r2_hidden(sK5,k1_xboole_0) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1650]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_27,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,X1)
% 11.68/2.00      | ~ r1_tarski(X0,X2)
% 11.68/2.00      | r1_tarski(k1_setfam_1(X1),X2) ),
% 11.68/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_972,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 11.68/2.00      | ~ r1_tarski(X0,X3)
% 11.68/2.00      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X3) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_27]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_974,plain,
% 11.68/2.00      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 11.68/2.00      | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 11.68/2.00      | ~ r1_tarski(sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_972]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_9,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.68/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_957,plain,
% 11.68/2.00      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 11.68/2.00      | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.68/2.00      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_64,plain,
% 11.68/2.00      ( r1_tarski(sK5,sK5) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_23,plain,
% 11.68/2.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 11.68/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_42,plain,
% 11.68/2.00      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_23]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_39,plain,
% 11.68/2.00      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_28,negated_conjecture,
% 11.68/2.00      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 11.68/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(contradiction,plain,
% 11.68/2.00      ( $false ),
% 11.68/2.00      inference(minisat,
% 11.68/2.00                [status(thm)],
% 11.68/2.00                [c_35427,c_23538,c_5442,c_1652,c_974,c_957,c_64,c_42,
% 11.68/2.00                 c_39,c_28]) ).
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  ------                               Statistics
% 11.68/2.00  
% 11.68/2.00  ------ Selected
% 11.68/2.00  
% 11.68/2.00  total_time:                             1.363
% 11.68/2.00  
%------------------------------------------------------------------------------
