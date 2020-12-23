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
% DateTime   : Thu Dec  3 11:41:36 EST 2020

% Result     : Theorem 27.51s
% Output     : CNFRefutation 27.51s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 338 expanded)
%              Number of clauses        :   62 (  91 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  471 (1515 expanded)
%              Number of equality atoms :  226 ( 688 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f42])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

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
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f99,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f102,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f88])).

fof(f103,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f102])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f100,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f87])).

fof(f101,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f100])).

fof(f12,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f44])).

fof(f77,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f77,f79])).

cnf(c_464,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1181,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_97339,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | X0 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_97341,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_97339])).

cnf(c_27,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1703,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_27,c_15])).

cnf(c_463,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_29417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_1703,c_463])).

cnf(c_29438,plain,
    ( X0 != X1
    | k1_xboole_0 = k2_enumset1(X2,X2,X2,X2)
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK4(k2_enumset1(X2,X2,X2,X2),X3)) = iProver_top
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X2,X2,X2,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29417])).

cnf(c_29440,plain,
    ( sK5 != sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) = iProver_top
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29438])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_931,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_924,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1644,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_924])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_925,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2248,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_925])).

cnf(c_6015,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_2248])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_913,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_914,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | k1_setfam_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_909,plain,
    ( k1_setfam_1(X0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1295,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_914,c_909])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1662,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_910])).

cnf(c_2269,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_1662])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_923,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2611,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_923])).

cnf(c_6381,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6015,c_2611])).

cnf(c_6646,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6381,c_924])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_932,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6009,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_932])).

cnf(c_6063,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6009,c_2611])).

cnf(c_6361,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6063,c_925])).

cnf(c_6662,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6646,c_6361])).

cnf(c_6664,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6662])).

cnf(c_6666,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6664])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,sK4(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1623,plain,
    ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1624,plain,
    ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) != iProver_top
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_1169,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1170,plain,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) != iProver_top
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_1120,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1121,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_1123,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_67,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_69,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_48,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_50,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_49,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_28,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_97341,c_29440,c_6666,c_1624,c_1170,c_1123,c_69,c_50,c_49,c_46,c_28])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.51/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.51/4.01  
% 27.51/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.51/4.01  
% 27.51/4.01  ------  iProver source info
% 27.51/4.01  
% 27.51/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.51/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.51/4.01  git: non_committed_changes: false
% 27.51/4.01  git: last_make_outside_of_git: false
% 27.51/4.01  
% 27.51/4.01  ------ 
% 27.51/4.01  ------ Parsing...
% 27.51/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.51/4.01  
% 27.51/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.51/4.01  
% 27.51/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.51/4.01  
% 27.51/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.51/4.01  ------ Proving...
% 27.51/4.01  ------ Problem Properties 
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  clauses                                 28
% 27.51/4.01  conjectures                             1
% 27.51/4.01  EPR                                     3
% 27.51/4.01  Horn                                    18
% 27.51/4.01  unary                                   7
% 27.51/4.01  binary                                  7
% 27.51/4.01  lits                                    65
% 27.51/4.01  lits eq                                 23
% 27.51/4.01  fd_pure                                 0
% 27.51/4.01  fd_pseudo                               0
% 27.51/4.01  fd_cond                                 2
% 27.51/4.01  fd_pseudo_cond                          9
% 27.51/4.01  AC symbols                              0
% 27.51/4.01  
% 27.51/4.01  ------ Input Options Time Limit: Unbounded
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  ------ 
% 27.51/4.01  Current options:
% 27.51/4.01  ------ 
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  ------ Proving...
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  % SZS status Theorem for theBenchmark.p
% 27.51/4.01  
% 27.51/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.51/4.01  
% 27.51/4.01  fof(f13,axiom,(
% 27.51/4.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f19,plain,(
% 27.51/4.01    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 27.51/4.01    inference(ennf_transformation,[],[f13])).
% 27.51/4.01  
% 27.51/4.01  fof(f20,plain,(
% 27.51/4.01    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 27.51/4.01    inference(flattening,[],[f19])).
% 27.51/4.01  
% 27.51/4.01  fof(f42,plain,(
% 27.51/4.01    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 27.51/4.01    introduced(choice_axiom,[])).
% 27.51/4.01  
% 27.51/4.01  fof(f43,plain,(
% 27.51/4.01    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 27.51/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f42])).
% 27.51/4.01  
% 27.51/4.01  fof(f75,plain,(
% 27.51/4.01    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f43])).
% 27.51/4.01  
% 27.51/4.01  fof(f4,axiom,(
% 27.51/4.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f33,plain,(
% 27.51/4.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 27.51/4.01    inference(nnf_transformation,[],[f4])).
% 27.51/4.01  
% 27.51/4.01  fof(f34,plain,(
% 27.51/4.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 27.51/4.01    inference(rectify,[],[f33])).
% 27.51/4.01  
% 27.51/4.01  fof(f35,plain,(
% 27.51/4.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 27.51/4.01    introduced(choice_axiom,[])).
% 27.51/4.01  
% 27.51/4.01  fof(f36,plain,(
% 27.51/4.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 27.51/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 27.51/4.01  
% 27.51/4.01  fof(f58,plain,(
% 27.51/4.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 27.51/4.01    inference(cnf_transformation,[],[f36])).
% 27.51/4.01  
% 27.51/4.01  fof(f6,axiom,(
% 27.51/4.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f68,plain,(
% 27.51/4.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f6])).
% 27.51/4.01  
% 27.51/4.01  fof(f7,axiom,(
% 27.51/4.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f69,plain,(
% 27.51/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f7])).
% 27.51/4.01  
% 27.51/4.01  fof(f8,axiom,(
% 27.51/4.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f70,plain,(
% 27.51/4.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f8])).
% 27.51/4.01  
% 27.51/4.01  fof(f78,plain,(
% 27.51/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.51/4.01    inference(definition_unfolding,[],[f69,f70])).
% 27.51/4.01  
% 27.51/4.01  fof(f79,plain,(
% 27.51/4.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 27.51/4.01    inference(definition_unfolding,[],[f68,f78])).
% 27.51/4.01  
% 27.51/4.01  fof(f83,plain,(
% 27.51/4.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 27.51/4.01    inference(definition_unfolding,[],[f58,f79])).
% 27.51/4.01  
% 27.51/4.01  fof(f99,plain,(
% 27.51/4.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 27.51/4.01    inference(equality_resolution,[],[f83])).
% 27.51/4.01  
% 27.51/4.01  fof(f1,axiom,(
% 27.51/4.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f16,plain,(
% 27.51/4.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.51/4.01    inference(ennf_transformation,[],[f1])).
% 27.51/4.01  
% 27.51/4.01  fof(f22,plain,(
% 27.51/4.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.51/4.01    inference(nnf_transformation,[],[f16])).
% 27.51/4.01  
% 27.51/4.01  fof(f23,plain,(
% 27.51/4.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.51/4.01    inference(rectify,[],[f22])).
% 27.51/4.01  
% 27.51/4.01  fof(f24,plain,(
% 27.51/4.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.51/4.01    introduced(choice_axiom,[])).
% 27.51/4.01  
% 27.51/4.01  fof(f25,plain,(
% 27.51/4.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.51/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 27.51/4.01  
% 27.51/4.01  fof(f47,plain,(
% 27.51/4.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f25])).
% 27.51/4.01  
% 27.51/4.01  fof(f2,axiom,(
% 27.51/4.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f26,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.51/4.01    inference(nnf_transformation,[],[f2])).
% 27.51/4.01  
% 27.51/4.01  fof(f27,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.51/4.01    inference(flattening,[],[f26])).
% 27.51/4.01  
% 27.51/4.01  fof(f28,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.51/4.01    inference(rectify,[],[f27])).
% 27.51/4.01  
% 27.51/4.01  fof(f29,plain,(
% 27.51/4.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.51/4.01    introduced(choice_axiom,[])).
% 27.51/4.01  
% 27.51/4.01  fof(f30,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.51/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 27.51/4.01  
% 27.51/4.01  fof(f49,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 27.51/4.01    inference(cnf_transformation,[],[f30])).
% 27.51/4.01  
% 27.51/4.01  fof(f94,plain,(
% 27.51/4.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 27.51/4.01    inference(equality_resolution,[],[f49])).
% 27.51/4.01  
% 27.51/4.01  fof(f50,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 27.51/4.01    inference(cnf_transformation,[],[f30])).
% 27.51/4.01  
% 27.51/4.01  fof(f93,plain,(
% 27.51/4.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 27.51/4.01    inference(equality_resolution,[],[f50])).
% 27.51/4.01  
% 27.51/4.01  fof(f5,axiom,(
% 27.51/4.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f37,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.51/4.01    inference(nnf_transformation,[],[f5])).
% 27.51/4.01  
% 27.51/4.01  fof(f38,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.51/4.01    inference(flattening,[],[f37])).
% 27.51/4.01  
% 27.51/4.01  fof(f39,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.51/4.01    inference(rectify,[],[f38])).
% 27.51/4.01  
% 27.51/4.01  fof(f40,plain,(
% 27.51/4.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 27.51/4.01    introduced(choice_axiom,[])).
% 27.51/4.01  
% 27.51/4.01  fof(f41,plain,(
% 27.51/4.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.51/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 27.51/4.01  
% 27.51/4.01  fof(f63,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.51/4.01    inference(cnf_transformation,[],[f41])).
% 27.51/4.01  
% 27.51/4.01  fof(f88,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.51/4.01    inference(definition_unfolding,[],[f63,f78])).
% 27.51/4.01  
% 27.51/4.01  fof(f102,plain,(
% 27.51/4.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 27.51/4.01    inference(equality_resolution,[],[f88])).
% 27.51/4.01  
% 27.51/4.01  fof(f103,plain,(
% 27.51/4.01    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 27.51/4.01    inference(equality_resolution,[],[f102])).
% 27.51/4.01  
% 27.51/4.01  fof(f64,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.51/4.01    inference(cnf_transformation,[],[f41])).
% 27.51/4.01  
% 27.51/4.01  fof(f87,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.51/4.01    inference(definition_unfolding,[],[f64,f78])).
% 27.51/4.01  
% 27.51/4.01  fof(f100,plain,(
% 27.51/4.01    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 27.51/4.01    inference(equality_resolution,[],[f87])).
% 27.51/4.01  
% 27.51/4.01  fof(f101,plain,(
% 27.51/4.01    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 27.51/4.01    inference(equality_resolution,[],[f100])).
% 27.51/4.01  
% 27.51/4.01  fof(f12,axiom,(
% 27.51/4.01    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f18,plain,(
% 27.51/4.01    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 27.51/4.01    inference(ennf_transformation,[],[f12])).
% 27.51/4.01  
% 27.51/4.01  fof(f74,plain,(
% 27.51/4.01    ( ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f18])).
% 27.51/4.01  
% 27.51/4.01  fof(f11,axiom,(
% 27.51/4.01    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f17,plain,(
% 27.51/4.01    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 27.51/4.01    inference(ennf_transformation,[],[f11])).
% 27.51/4.01  
% 27.51/4.01  fof(f73,plain,(
% 27.51/4.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f17])).
% 27.51/4.01  
% 27.51/4.01  fof(f3,axiom,(
% 27.51/4.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f31,plain,(
% 27.51/4.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.51/4.01    inference(nnf_transformation,[],[f3])).
% 27.51/4.01  
% 27.51/4.01  fof(f32,plain,(
% 27.51/4.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.51/4.01    inference(flattening,[],[f31])).
% 27.51/4.01  
% 27.51/4.01  fof(f57,plain,(
% 27.51/4.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f32])).
% 27.51/4.01  
% 27.51/4.01  fof(f48,plain,(
% 27.51/4.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 27.51/4.01    inference(cnf_transformation,[],[f25])).
% 27.51/4.01  
% 27.51/4.01  fof(f76,plain,(
% 27.51/4.01    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK4(X0,X1))) )),
% 27.51/4.01    inference(cnf_transformation,[],[f43])).
% 27.51/4.01  
% 27.51/4.01  fof(f55,plain,(
% 27.51/4.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.51/4.01    inference(cnf_transformation,[],[f32])).
% 27.51/4.01  
% 27.51/4.01  fof(f96,plain,(
% 27.51/4.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.51/4.01    inference(equality_resolution,[],[f55])).
% 27.51/4.01  
% 27.51/4.01  fof(f62,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 27.51/4.01    inference(cnf_transformation,[],[f41])).
% 27.51/4.01  
% 27.51/4.01  fof(f89,plain,(
% 27.51/4.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.51/4.01    inference(definition_unfolding,[],[f62,f78])).
% 27.51/4.01  
% 27.51/4.01  fof(f104,plain,(
% 27.51/4.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 27.51/4.01    inference(equality_resolution,[],[f89])).
% 27.51/4.01  
% 27.51/4.01  fof(f14,conjecture,(
% 27.51/4.01    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 27.51/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.51/4.01  
% 27.51/4.01  fof(f15,negated_conjecture,(
% 27.51/4.01    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 27.51/4.01    inference(negated_conjecture,[],[f14])).
% 27.51/4.01  
% 27.51/4.01  fof(f21,plain,(
% 27.51/4.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 27.51/4.01    inference(ennf_transformation,[],[f15])).
% 27.51/4.01  
% 27.51/4.01  fof(f44,plain,(
% 27.51/4.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 27.51/4.01    introduced(choice_axiom,[])).
% 27.51/4.01  
% 27.51/4.01  fof(f45,plain,(
% 27.51/4.01    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 27.51/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f44])).
% 27.51/4.01  
% 27.51/4.01  fof(f77,plain,(
% 27.51/4.01    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 27.51/4.01    inference(cnf_transformation,[],[f45])).
% 27.51/4.01  
% 27.51/4.01  fof(f91,plain,(
% 27.51/4.01    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 27.51/4.01    inference(definition_unfolding,[],[f77,f79])).
% 27.51/4.01  
% 27.51/4.01  cnf(c_464,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.51/4.01      theory(equality) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1181,plain,
% 27.51/4.01      ( r2_hidden(X0,X1)
% 27.51/4.01      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
% 27.51/4.01      | X0 != X2
% 27.51/4.01      | X1 != k2_enumset1(X2,X2,X2,X2) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_464]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_97339,plain,
% 27.51/4.01      ( r2_hidden(X0,k1_xboole_0)
% 27.51/4.01      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 27.51/4.01      | X0 != sK5
% 27.51/4.01      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_1181]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_97341,plain,
% 27.51/4.01      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 27.51/4.01      | r2_hidden(sK5,k1_xboole_0)
% 27.51/4.01      | sK5 != sK5
% 27.51/4.01      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_97339]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_27,plain,
% 27.51/4.01      ( r2_hidden(sK4(X0,X1),X0)
% 27.51/4.01      | r1_tarski(X1,k1_setfam_1(X0))
% 27.51/4.01      | k1_xboole_0 = X0 ),
% 27.51/4.01      inference(cnf_transformation,[],[f75]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_15,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 27.51/4.01      inference(cnf_transformation,[],[f99]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1703,plain,
% 27.51/4.01      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 27.51/4.01      | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 27.51/4.01      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 27.51/4.01      inference(resolution,[status(thm)],[c_27,c_15]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_463,plain,
% 27.51/4.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.51/4.01      theory(equality) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_29417,plain,
% 27.51/4.01      ( ~ r1_tarski(X0,X1)
% 27.51/4.01      | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
% 27.51/4.01      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 27.51/4.01      | X2 != X0
% 27.51/4.01      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 27.51/4.01      inference(resolution,[status(thm)],[c_1703,c_463]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_29438,plain,
% 27.51/4.01      ( X0 != X1
% 27.51/4.01      | k1_xboole_0 = k2_enumset1(X2,X2,X2,X2)
% 27.51/4.01      | r1_tarski(X1,X2) != iProver_top
% 27.51/4.01      | r1_tarski(X0,sK4(k2_enumset1(X2,X2,X2,X2),X3)) = iProver_top
% 27.51/4.01      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X2,X2,X2,X2))) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_29417]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_29440,plain,
% 27.51/4.01      ( sK5 != sK5
% 27.51/4.01      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
% 27.51/4.01      | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) = iProver_top
% 27.51/4.01      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
% 27.51/4.01      | r1_tarski(sK5,sK5) != iProver_top ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_29438]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1,plain,
% 27.51/4.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 27.51/4.01      inference(cnf_transformation,[],[f47]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_931,plain,
% 27.51/4.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 27.51/4.01      | r1_tarski(X0,X1) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_8,plain,
% 27.51/4.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 27.51/4.01      inference(cnf_transformation,[],[f94]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_924,plain,
% 27.51/4.01      ( r2_hidden(X0,X1) = iProver_top
% 27.51/4.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1644,plain,
% 27.51/4.01      ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
% 27.51/4.01      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_931,c_924]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_7,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 27.51/4.01      inference(cnf_transformation,[],[f93]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_925,plain,
% 27.51/4.01      ( r2_hidden(X0,X1) != iProver_top
% 27.51/4.01      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_2248,plain,
% 27.51/4.01      ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X1) != iProver_top
% 27.51/4.01      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_931,c_925]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6015,plain,
% 27.51/4.01      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_1644,c_2248]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_20,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 27.51/4.01      inference(cnf_transformation,[],[f103]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_913,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_19,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 27.51/4.01      inference(cnf_transformation,[],[f101]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_914,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_25,plain,
% 27.51/4.01      ( ~ r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0 ),
% 27.51/4.01      inference(cnf_transformation,[],[f74]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_909,plain,
% 27.51/4.01      ( k1_setfam_1(X0) = k1_xboole_0
% 27.51/4.01      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1295,plain,
% 27.51/4.01      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_914,c_909]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_24,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 27.51/4.01      inference(cnf_transformation,[],[f73]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_910,plain,
% 27.51/4.01      ( r2_hidden(X0,X1) != iProver_top
% 27.51/4.01      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1662,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,k1_xboole_0)) != iProver_top
% 27.51/4.01      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_1295,c_910]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_2269,plain,
% 27.51/4.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_913,c_1662]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_9,plain,
% 27.51/4.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 27.51/4.01      inference(cnf_transformation,[],[f57]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_923,plain,
% 27.51/4.01      ( X0 = X1
% 27.51/4.01      | r1_tarski(X1,X0) != iProver_top
% 27.51/4.01      | r1_tarski(X0,X1) != iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_2611,plain,
% 27.51/4.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_2269,c_923]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6381,plain,
% 27.51/4.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_6015,c_2611]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6646,plain,
% 27.51/4.01      ( r2_hidden(X0,X1) = iProver_top
% 27.51/4.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_6381,c_924]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_0,plain,
% 27.51/4.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 27.51/4.01      inference(cnf_transformation,[],[f48]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_932,plain,
% 27.51/4.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 27.51/4.01      | r1_tarski(X0,X1) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6009,plain,
% 27.51/4.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_1644,c_932]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6063,plain,
% 27.51/4.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_6009,c_2611]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6361,plain,
% 27.51/4.01      ( r2_hidden(X0,X1) != iProver_top
% 27.51/4.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.51/4.01      inference(superposition,[status(thm)],[c_6063,c_925]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6662,plain,
% 27.51/4.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.51/4.01      inference(global_propositional_subsumption,
% 27.51/4.01                [status(thm)],
% 27.51/4.01                [c_6646,c_6361]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6664,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 27.51/4.01      inference(predicate_to_equality_rev,[status(thm)],[c_6662]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_6666,plain,
% 27.51/4.01      ( ~ r2_hidden(sK5,k1_xboole_0) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_6664]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_26,plain,
% 27.51/4.01      ( ~ r1_tarski(X0,sK4(X1,X0))
% 27.51/4.01      | r1_tarski(X0,k1_setfam_1(X1))
% 27.51/4.01      | k1_xboole_0 = X1 ),
% 27.51/4.01      inference(cnf_transformation,[],[f76]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1623,plain,
% 27.51/4.01      ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 27.51/4.01      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 27.51/4.01      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_26]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1624,plain,
% 27.51/4.01      ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5)
% 27.51/4.01      | r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) != iProver_top
% 27.51/4.01      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1169,plain,
% 27.51/4.01      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 27.51/4.01      | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 27.51/4.01      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_9]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1170,plain,
% 27.51/4.01      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 27.51/4.01      | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) != iProver_top
% 27.51/4.01      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) != iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_1169]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1120,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 27.51/4.01      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_24]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1121,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 27.51/4.01      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_1123,plain,
% 27.51/4.01      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 27.51/4.01      | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) = iProver_top ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_1121]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_11,plain,
% 27.51/4.01      ( r1_tarski(X0,X0) ),
% 27.51/4.01      inference(cnf_transformation,[],[f96]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_67,plain,
% 27.51/4.01      ( r1_tarski(X0,X0) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_69,plain,
% 27.51/4.01      ( r1_tarski(sK5,sK5) = iProver_top ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_67]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_48,plain,
% 27.51/4.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 27.51/4.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_50,plain,
% 27.51/4.01      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_48]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_49,plain,
% 27.51/4.01      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_20]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_21,plain,
% 27.51/4.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 27.51/4.01      inference(cnf_transformation,[],[f104]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_46,plain,
% 27.51/4.01      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 27.51/4.01      inference(instantiation,[status(thm)],[c_21]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(c_28,negated_conjecture,
% 27.51/4.01      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 27.51/4.01      inference(cnf_transformation,[],[f91]) ).
% 27.51/4.01  
% 27.51/4.01  cnf(contradiction,plain,
% 27.51/4.01      ( $false ),
% 27.51/4.01      inference(minisat,
% 27.51/4.01                [status(thm)],
% 27.51/4.01                [c_97341,c_29440,c_6666,c_1624,c_1170,c_1123,c_69,c_50,
% 27.51/4.01                 c_49,c_46,c_28]) ).
% 27.51/4.01  
% 27.51/4.01  
% 27.51/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.51/4.01  
% 27.51/4.01  ------                               Statistics
% 27.51/4.01  
% 27.51/4.01  ------ Selected
% 27.51/4.01  
% 27.51/4.01  total_time:                             3.029
% 27.51/4.01  
%------------------------------------------------------------------------------
