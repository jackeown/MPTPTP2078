%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:33 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 657 expanded)
%              Number of clauses        :   76 ( 113 expanded)
%              Number of leaves         :   31 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          :  553 (1529 expanded)
%              Number of equality atoms :  250 ( 718 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f48])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f111,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f110])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f111])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f82,f112])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f100,f112])).

fof(f115,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f113])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f113])).

fof(f121,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f73,f114])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f113])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f122,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f74,f114])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f46])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f68,f113])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f114,f112,f112])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f33,f40])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f130,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f98,f79])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f130])).

fof(f52,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X0
            & sK3(X0,X1,X2,X3,X4,X5) != X1
            & sK3(X0,X1,X2,X3,X4,X5) != X2
            & sK3(X0,X1,X2,X3,X4,X5) != X3
            & sK3(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK3(X0,X1,X2,X3,X4,X5) = X0
          | sK3(X0,X1,X2,X3,X4,X5) = X1
          | sK3(X0,X1,X2,X3,X4,X5) = X2
          | sK3(X0,X1,X2,X3,X4,X5) = X3
          | sK3(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X0
              & sK3(X0,X1,X2,X3,X4,X5) != X1
              & sK3(X0,X1,X2,X3,X4,X5) != X2
              & sK3(X0,X1,X2,X3,X4,X5) != X3
              & sK3(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK3(X0,X1,X2,X3,X4,X5) = X0
            | sK3(X0,X1,X2,X3,X4,X5) = X1
            | sK3(X0,X1,X2,X3,X4,X5) = X2
            | sK3(X0,X1,X2,X3,X4,X5) = X3
            | sK3(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f87,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f136,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f87])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f113])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK6)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK6)))
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(sK5,X2)),k3_xboole_0(k5_relat_1(X0,sK5),k5_relat_1(X0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK4,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK4,X1),k5_relat_1(sK4,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ~ r1_tarski(k5_relat_1(sK4,k3_xboole_0(sK5,sK6)),k3_xboole_0(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))
    & v1_relat_1(sK6)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f61,f60,f59])).

fof(f109,plain,(
    ~ r1_tarski(k5_relat_1(sK4,k3_xboole_0(sK5,sK6)),k3_xboole_0(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f62])).

fof(f131,plain,(
    ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) ),
    inference(definition_unfolding,[],[f109,f113,f113])).

fof(f106,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f70,f113])).

fof(f108,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f132,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X1,X2,X3,X4,X5) ) ),
    inference(equality_resolution,[],[f91])).

cnf(c_12,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_3368,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3348,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5288,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3348])).

cnf(c_8351,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3368,c_5288])).

cnf(c_9,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3371,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4028,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3371])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3372,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5126,plain,
    ( k1_setfam_1(k4_enumset1(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4028,c_3372])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3370,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3843,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3370])).

cnf(c_0,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3379,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3376,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6452,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3379,c_3376])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3377,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3369,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4280,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3377,c_3369])).

cnf(c_7860,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6452,c_4280])).

cnf(c_7988,plain,
    ( k1_setfam_1(k4_enumset1(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3843,c_7860])).

cnf(c_11424,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5126,c_7988])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),X1))) != k4_enumset1(X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3363,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6644,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) != k4_enumset1(X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3363])).

cnf(c_31,plain,
    ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_3349,plain,
    ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_3352,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X4,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4456,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3349,c_3352])).

cnf(c_10512,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) != k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6644,c_4456])).

cnf(c_11439,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11424,c_10512])).

cnf(c_12527,plain,
    ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8351,c_11439])).

cnf(c_36,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_215,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_35,c_32])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_3343,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3373,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_37,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_3347,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6959,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) != iProver_top
    | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3373,c_3347])).

cnf(c_40,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_41,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_42,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_44,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3833,plain,
    ( ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6))
    | ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5))
    | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3834,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) != iProver_top
    | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5)) != iProver_top
    | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3833])).

cnf(c_3658,plain,
    ( r1_tarski(k5_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_relat_1(X0,X1))
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_4535,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5))
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3658])).

cnf(c_4538,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5)) = iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4535])).

cnf(c_6,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_4881,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4882,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4881])).

cnf(c_7425,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6959,c_41,c_42,c_44,c_3834,c_4538,c_4882])).

cnf(c_7430,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_7425])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_43,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3951,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6))
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_3952,plain,
    ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) = iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3951])).

cnf(c_7433,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7430,c_41,c_42,c_43,c_44,c_3834,c_3952,c_4538,c_4882])).

cnf(c_12537,plain,
    ( r2_hidden(sK6,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12527,c_7433])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X0,X5) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3356,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X0,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4989,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X2,X3,X4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3349,c_3356])).

cnf(c_12906,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12537,c_4989])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.75/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/0.99  
% 3.75/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.99  
% 3.75/0.99  ------  iProver source info
% 3.75/0.99  
% 3.75/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.99  git: non_committed_changes: false
% 3.75/0.99  git: last_make_outside_of_git: false
% 3.75/0.99  
% 3.75/0.99  ------ 
% 3.75/0.99  
% 3.75/0.99  ------ Input Options
% 3.75/0.99  
% 3.75/0.99  --out_options                           all
% 3.75/0.99  --tptp_safe_out                         true
% 3.75/0.99  --problem_path                          ""
% 3.75/0.99  --include_path                          ""
% 3.75/0.99  --clausifier                            res/vclausify_rel
% 3.75/0.99  --clausifier_options                    --mode clausify
% 3.75/0.99  --stdin                                 false
% 3.75/0.99  --stats_out                             all
% 3.75/0.99  
% 3.75/0.99  ------ General Options
% 3.75/0.99  
% 3.75/0.99  --fof                                   false
% 3.75/0.99  --time_out_real                         305.
% 3.75/0.99  --time_out_virtual                      -1.
% 3.75/0.99  --symbol_type_check                     false
% 3.75/0.99  --clausify_out                          false
% 3.75/0.99  --sig_cnt_out                           false
% 3.75/0.99  --trig_cnt_out                          false
% 3.75/0.99  --trig_cnt_out_tolerance                1.
% 3.75/0.99  --trig_cnt_out_sk_spl                   false
% 3.75/0.99  --abstr_cl_out                          false
% 3.75/0.99  
% 3.75/0.99  ------ Global Options
% 3.75/0.99  
% 3.75/0.99  --schedule                              default
% 3.75/0.99  --add_important_lit                     false
% 3.75/0.99  --prop_solver_per_cl                    1000
% 3.75/0.99  --min_unsat_core                        false
% 3.75/0.99  --soft_assumptions                      false
% 3.75/0.99  --soft_lemma_size                       3
% 3.75/0.99  --prop_impl_unit_size                   0
% 3.75/0.99  --prop_impl_unit                        []
% 3.75/0.99  --share_sel_clauses                     true
% 3.75/0.99  --reset_solvers                         false
% 3.75/0.99  --bc_imp_inh                            [conj_cone]
% 3.75/0.99  --conj_cone_tolerance                   3.
% 3.75/0.99  --extra_neg_conj                        none
% 3.75/0.99  --large_theory_mode                     true
% 3.75/0.99  --prolific_symb_bound                   200
% 3.75/0.99  --lt_threshold                          2000
% 3.75/0.99  --clause_weak_htbl                      true
% 3.75/0.99  --gc_record_bc_elim                     false
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing Options
% 3.75/0.99  
% 3.75/0.99  --preprocessing_flag                    true
% 3.75/0.99  --time_out_prep_mult                    0.1
% 3.75/0.99  --splitting_mode                        input
% 3.75/0.99  --splitting_grd                         true
% 3.75/0.99  --splitting_cvd                         false
% 3.75/0.99  --splitting_cvd_svl                     false
% 3.75/0.99  --splitting_nvd                         32
% 3.75/0.99  --sub_typing                            true
% 3.75/0.99  --prep_gs_sim                           true
% 3.75/0.99  --prep_unflatten                        true
% 3.75/0.99  --prep_res_sim                          true
% 3.75/0.99  --prep_upred                            true
% 3.75/0.99  --prep_sem_filter                       exhaustive
% 3.75/0.99  --prep_sem_filter_out                   false
% 3.75/0.99  --pred_elim                             true
% 3.75/0.99  --res_sim_input                         true
% 3.75/0.99  --eq_ax_congr_red                       true
% 3.75/0.99  --pure_diseq_elim                       true
% 3.75/0.99  --brand_transform                       false
% 3.75/0.99  --non_eq_to_eq                          false
% 3.75/0.99  --prep_def_merge                        true
% 3.75/0.99  --prep_def_merge_prop_impl              false
% 3.75/0.99  --prep_def_merge_mbd                    true
% 3.75/0.99  --prep_def_merge_tr_red                 false
% 3.75/0.99  --prep_def_merge_tr_cl                  false
% 3.75/0.99  --smt_preprocessing                     true
% 3.75/0.99  --smt_ac_axioms                         fast
% 3.75/0.99  --preprocessed_out                      false
% 3.75/0.99  --preprocessed_stats                    false
% 3.75/0.99  
% 3.75/0.99  ------ Abstraction refinement Options
% 3.75/0.99  
% 3.75/0.99  --abstr_ref                             []
% 3.75/0.99  --abstr_ref_prep                        false
% 3.75/0.99  --abstr_ref_until_sat                   false
% 3.75/0.99  --abstr_ref_sig_restrict                funpre
% 3.75/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.99  --abstr_ref_under                       []
% 3.75/0.99  
% 3.75/0.99  ------ SAT Options
% 3.75/0.99  
% 3.75/0.99  --sat_mode                              false
% 3.75/0.99  --sat_fm_restart_options                ""
% 3.75/0.99  --sat_gr_def                            false
% 3.75/0.99  --sat_epr_types                         true
% 3.75/0.99  --sat_non_cyclic_types                  false
% 3.75/0.99  --sat_finite_models                     false
% 3.75/0.99  --sat_fm_lemmas                         false
% 3.75/0.99  --sat_fm_prep                           false
% 3.75/0.99  --sat_fm_uc_incr                        true
% 3.75/0.99  --sat_out_model                         small
% 3.75/0.99  --sat_out_clauses                       false
% 3.75/0.99  
% 3.75/0.99  ------ QBF Options
% 3.75/0.99  
% 3.75/0.99  --qbf_mode                              false
% 3.75/0.99  --qbf_elim_univ                         false
% 3.75/0.99  --qbf_dom_inst                          none
% 3.75/0.99  --qbf_dom_pre_inst                      false
% 3.75/0.99  --qbf_sk_in                             false
% 3.75/0.99  --qbf_pred_elim                         true
% 3.75/0.99  --qbf_split                             512
% 3.75/0.99  
% 3.75/0.99  ------ BMC1 Options
% 3.75/0.99  
% 3.75/0.99  --bmc1_incremental                      false
% 3.75/0.99  --bmc1_axioms                           reachable_all
% 3.75/0.99  --bmc1_min_bound                        0
% 3.75/0.99  --bmc1_max_bound                        -1
% 3.75/0.99  --bmc1_max_bound_default                -1
% 3.75/0.99  --bmc1_symbol_reachability              true
% 3.75/0.99  --bmc1_property_lemmas                  false
% 3.75/0.99  --bmc1_k_induction                      false
% 3.75/0.99  --bmc1_non_equiv_states                 false
% 3.75/0.99  --bmc1_deadlock                         false
% 3.75/0.99  --bmc1_ucm                              false
% 3.75/0.99  --bmc1_add_unsat_core                   none
% 3.75/0.99  --bmc1_unsat_core_children              false
% 3.75/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.99  --bmc1_out_stat                         full
% 3.75/0.99  --bmc1_ground_init                      false
% 3.75/0.99  --bmc1_pre_inst_next_state              false
% 3.75/0.99  --bmc1_pre_inst_state                   false
% 3.75/0.99  --bmc1_pre_inst_reach_state             false
% 3.75/0.99  --bmc1_out_unsat_core                   false
% 3.75/0.99  --bmc1_aig_witness_out                  false
% 3.75/0.99  --bmc1_verbose                          false
% 3.75/0.99  --bmc1_dump_clauses_tptp                false
% 3.75/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.99  --bmc1_dump_file                        -
% 3.75/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.99  --bmc1_ucm_extend_mode                  1
% 3.75/0.99  --bmc1_ucm_init_mode                    2
% 3.75/0.99  --bmc1_ucm_cone_mode                    none
% 3.75/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.99  --bmc1_ucm_relax_model                  4
% 3.75/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.99  --bmc1_ucm_layered_model                none
% 3.75/0.99  --bmc1_ucm_max_lemma_size               10
% 3.75/0.99  
% 3.75/0.99  ------ AIG Options
% 3.75/0.99  
% 3.75/0.99  --aig_mode                              false
% 3.75/0.99  
% 3.75/0.99  ------ Instantiation Options
% 3.75/0.99  
% 3.75/0.99  --instantiation_flag                    true
% 3.75/0.99  --inst_sos_flag                         false
% 3.75/0.99  --inst_sos_phase                        true
% 3.75/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.99  --inst_lit_sel_side                     num_symb
% 3.75/0.99  --inst_solver_per_active                1400
% 3.75/0.99  --inst_solver_calls_frac                1.
% 3.75/0.99  --inst_passive_queue_type               priority_queues
% 3.75/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.99  --inst_passive_queues_freq              [25;2]
% 3.75/0.99  --inst_dismatching                      true
% 3.75/0.99  --inst_eager_unprocessed_to_passive     true
% 3.75/0.99  --inst_prop_sim_given                   true
% 3.75/0.99  --inst_prop_sim_new                     false
% 3.75/0.99  --inst_subs_new                         false
% 3.75/0.99  --inst_eq_res_simp                      false
% 3.75/0.99  --inst_subs_given                       false
% 3.75/0.99  --inst_orphan_elimination               true
% 3.75/0.99  --inst_learning_loop_flag               true
% 3.75/0.99  --inst_learning_start                   3000
% 3.75/0.99  --inst_learning_factor                  2
% 3.75/0.99  --inst_start_prop_sim_after_learn       3
% 3.75/0.99  --inst_sel_renew                        solver
% 3.75/0.99  --inst_lit_activity_flag                true
% 3.75/0.99  --inst_restr_to_given                   false
% 3.75/0.99  --inst_activity_threshold               500
% 3.75/0.99  --inst_out_proof                        true
% 3.75/0.99  
% 3.75/0.99  ------ Resolution Options
% 3.75/0.99  
% 3.75/0.99  --resolution_flag                       true
% 3.75/0.99  --res_lit_sel                           adaptive
% 3.75/0.99  --res_lit_sel_side                      none
% 3.75/0.99  --res_ordering                          kbo
% 3.75/0.99  --res_to_prop_solver                    active
% 3.75/0.99  --res_prop_simpl_new                    false
% 3.75/0.99  --res_prop_simpl_given                  true
% 3.75/0.99  --res_passive_queue_type                priority_queues
% 3.75/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.99  --res_passive_queues_freq               [15;5]
% 3.75/0.99  --res_forward_subs                      full
% 3.75/0.99  --res_backward_subs                     full
% 3.75/0.99  --res_forward_subs_resolution           true
% 3.75/0.99  --res_backward_subs_resolution          true
% 3.75/0.99  --res_orphan_elimination                true
% 3.75/0.99  --res_time_limit                        2.
% 3.75/0.99  --res_out_proof                         true
% 3.75/0.99  
% 3.75/0.99  ------ Superposition Options
% 3.75/0.99  
% 3.75/0.99  --superposition_flag                    true
% 3.75/0.99  --sup_passive_queue_type                priority_queues
% 3.75/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.99  --demod_completeness_check              fast
% 3.75/0.99  --demod_use_ground                      true
% 3.75/0.99  --sup_to_prop_solver                    passive
% 3.75/0.99  --sup_prop_simpl_new                    true
% 3.75/0.99  --sup_prop_simpl_given                  true
% 3.75/0.99  --sup_fun_splitting                     false
% 3.75/0.99  --sup_smt_interval                      50000
% 3.75/0.99  
% 3.75/0.99  ------ Superposition Simplification Setup
% 3.75/0.99  
% 3.75/0.99  --sup_indices_passive                   []
% 3.75/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.99  --sup_full_bw                           [BwDemod]
% 3.75/0.99  --sup_immed_triv                        [TrivRules]
% 3.75/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.99  --sup_immed_bw_main                     []
% 3.75/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.99  
% 3.75/0.99  ------ Combination Options
% 3.75/0.99  
% 3.75/0.99  --comb_res_mult                         3
% 3.75/0.99  --comb_sup_mult                         2
% 3.75/0.99  --comb_inst_mult                        10
% 3.75/0.99  
% 3.75/0.99  ------ Debug Options
% 3.75/0.99  
% 3.75/0.99  --dbg_backtrace                         false
% 3.75/0.99  --dbg_dump_prop_clauses                 false
% 3.75/0.99  --dbg_dump_prop_clauses_file            -
% 3.75/0.99  --dbg_out_stat                          false
% 3.75/0.99  ------ Parsing...
% 3.75/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.99  ------ Proving...
% 3.75/0.99  ------ Problem Properties 
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  clauses                                 39
% 3.75/0.99  conjectures                             4
% 3.75/0.99  EPR                                     13
% 3.75/0.99  Horn                                    33
% 3.75/0.99  unary                                   10
% 3.75/0.99  binary                                  15
% 3.75/0.99  lits                                    91
% 3.75/0.99  lits eq                                 23
% 3.75/0.99  fd_pure                                 0
% 3.75/0.99  fd_pseudo                               0
% 3.75/0.99  fd_cond                                 1
% 3.75/0.99  fd_pseudo_cond                          3
% 3.75/0.99  AC symbols                              0
% 3.75/0.99  
% 3.75/0.99  ------ Schedule dynamic 5 is on 
% 3.75/0.99  
% 3.75/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  ------ 
% 3.75/0.99  Current options:
% 3.75/0.99  ------ 
% 3.75/0.99  
% 3.75/0.99  ------ Input Options
% 3.75/0.99  
% 3.75/0.99  --out_options                           all
% 3.75/0.99  --tptp_safe_out                         true
% 3.75/0.99  --problem_path                          ""
% 3.75/0.99  --include_path                          ""
% 3.75/0.99  --clausifier                            res/vclausify_rel
% 3.75/0.99  --clausifier_options                    --mode clausify
% 3.75/0.99  --stdin                                 false
% 3.75/0.99  --stats_out                             all
% 3.75/0.99  
% 3.75/0.99  ------ General Options
% 3.75/0.99  
% 3.75/0.99  --fof                                   false
% 3.75/0.99  --time_out_real                         305.
% 3.75/0.99  --time_out_virtual                      -1.
% 3.75/0.99  --symbol_type_check                     false
% 3.75/0.99  --clausify_out                          false
% 3.75/0.99  --sig_cnt_out                           false
% 3.75/0.99  --trig_cnt_out                          false
% 3.75/0.99  --trig_cnt_out_tolerance                1.
% 3.75/0.99  --trig_cnt_out_sk_spl                   false
% 3.75/0.99  --abstr_cl_out                          false
% 3.75/0.99  
% 3.75/0.99  ------ Global Options
% 3.75/0.99  
% 3.75/0.99  --schedule                              default
% 3.75/0.99  --add_important_lit                     false
% 3.75/0.99  --prop_solver_per_cl                    1000
% 3.75/0.99  --min_unsat_core                        false
% 3.75/0.99  --soft_assumptions                      false
% 3.75/0.99  --soft_lemma_size                       3
% 3.75/0.99  --prop_impl_unit_size                   0
% 3.75/0.99  --prop_impl_unit                        []
% 3.75/0.99  --share_sel_clauses                     true
% 3.75/0.99  --reset_solvers                         false
% 3.75/0.99  --bc_imp_inh                            [conj_cone]
% 3.75/0.99  --conj_cone_tolerance                   3.
% 3.75/0.99  --extra_neg_conj                        none
% 3.75/0.99  --large_theory_mode                     true
% 3.75/0.99  --prolific_symb_bound                   200
% 3.75/0.99  --lt_threshold                          2000
% 3.75/0.99  --clause_weak_htbl                      true
% 3.75/0.99  --gc_record_bc_elim                     false
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing Options
% 3.75/0.99  
% 3.75/0.99  --preprocessing_flag                    true
% 3.75/0.99  --time_out_prep_mult                    0.1
% 3.75/0.99  --splitting_mode                        input
% 3.75/0.99  --splitting_grd                         true
% 3.75/0.99  --splitting_cvd                         false
% 3.75/0.99  --splitting_cvd_svl                     false
% 3.75/0.99  --splitting_nvd                         32
% 3.75/0.99  --sub_typing                            true
% 3.75/0.99  --prep_gs_sim                           true
% 3.75/0.99  --prep_unflatten                        true
% 3.75/0.99  --prep_res_sim                          true
% 3.75/0.99  --prep_upred                            true
% 3.75/0.99  --prep_sem_filter                       exhaustive
% 3.75/0.99  --prep_sem_filter_out                   false
% 3.75/0.99  --pred_elim                             true
% 3.75/0.99  --res_sim_input                         true
% 3.75/0.99  --eq_ax_congr_red                       true
% 3.75/0.99  --pure_diseq_elim                       true
% 3.75/0.99  --brand_transform                       false
% 3.75/0.99  --non_eq_to_eq                          false
% 3.75/0.99  --prep_def_merge                        true
% 3.75/0.99  --prep_def_merge_prop_impl              false
% 3.75/0.99  --prep_def_merge_mbd                    true
% 3.75/0.99  --prep_def_merge_tr_red                 false
% 3.75/0.99  --prep_def_merge_tr_cl                  false
% 3.75/0.99  --smt_preprocessing                     true
% 3.75/0.99  --smt_ac_axioms                         fast
% 3.75/0.99  --preprocessed_out                      false
% 3.75/0.99  --preprocessed_stats                    false
% 3.75/0.99  
% 3.75/0.99  ------ Abstraction refinement Options
% 3.75/0.99  
% 3.75/0.99  --abstr_ref                             []
% 3.75/0.99  --abstr_ref_prep                        false
% 3.75/0.99  --abstr_ref_until_sat                   false
% 3.75/0.99  --abstr_ref_sig_restrict                funpre
% 3.75/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.99  --abstr_ref_under                       []
% 3.75/0.99  
% 3.75/0.99  ------ SAT Options
% 3.75/0.99  
% 3.75/0.99  --sat_mode                              false
% 3.75/0.99  --sat_fm_restart_options                ""
% 3.75/0.99  --sat_gr_def                            false
% 3.75/0.99  --sat_epr_types                         true
% 3.75/0.99  --sat_non_cyclic_types                  false
% 3.75/0.99  --sat_finite_models                     false
% 3.75/0.99  --sat_fm_lemmas                         false
% 3.75/0.99  --sat_fm_prep                           false
% 3.75/0.99  --sat_fm_uc_incr                        true
% 3.75/0.99  --sat_out_model                         small
% 3.75/0.99  --sat_out_clauses                       false
% 3.75/0.99  
% 3.75/0.99  ------ QBF Options
% 3.75/0.99  
% 3.75/0.99  --qbf_mode                              false
% 3.75/0.99  --qbf_elim_univ                         false
% 3.75/0.99  --qbf_dom_inst                          none
% 3.75/0.99  --qbf_dom_pre_inst                      false
% 3.75/0.99  --qbf_sk_in                             false
% 3.75/0.99  --qbf_pred_elim                         true
% 3.75/0.99  --qbf_split                             512
% 3.75/0.99  
% 3.75/0.99  ------ BMC1 Options
% 3.75/0.99  
% 3.75/0.99  --bmc1_incremental                      false
% 3.75/0.99  --bmc1_axioms                           reachable_all
% 3.75/0.99  --bmc1_min_bound                        0
% 3.75/0.99  --bmc1_max_bound                        -1
% 3.75/0.99  --bmc1_max_bound_default                -1
% 3.75/0.99  --bmc1_symbol_reachability              true
% 3.75/0.99  --bmc1_property_lemmas                  false
% 3.75/0.99  --bmc1_k_induction                      false
% 3.75/0.99  --bmc1_non_equiv_states                 false
% 3.75/0.99  --bmc1_deadlock                         false
% 3.75/0.99  --bmc1_ucm                              false
% 3.75/0.99  --bmc1_add_unsat_core                   none
% 3.75/0.99  --bmc1_unsat_core_children              false
% 3.75/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.99  --bmc1_out_stat                         full
% 3.75/0.99  --bmc1_ground_init                      false
% 3.75/0.99  --bmc1_pre_inst_next_state              false
% 3.75/0.99  --bmc1_pre_inst_state                   false
% 3.75/0.99  --bmc1_pre_inst_reach_state             false
% 3.75/0.99  --bmc1_out_unsat_core                   false
% 3.75/0.99  --bmc1_aig_witness_out                  false
% 3.75/0.99  --bmc1_verbose                          false
% 3.75/0.99  --bmc1_dump_clauses_tptp                false
% 3.75/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.99  --bmc1_dump_file                        -
% 3.75/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.99  --bmc1_ucm_extend_mode                  1
% 3.75/0.99  --bmc1_ucm_init_mode                    2
% 3.75/0.99  --bmc1_ucm_cone_mode                    none
% 3.75/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.99  --bmc1_ucm_relax_model                  4
% 3.75/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.99  --bmc1_ucm_layered_model                none
% 3.75/0.99  --bmc1_ucm_max_lemma_size               10
% 3.75/0.99  
% 3.75/0.99  ------ AIG Options
% 3.75/0.99  
% 3.75/0.99  --aig_mode                              false
% 3.75/0.99  
% 3.75/0.99  ------ Instantiation Options
% 3.75/0.99  
% 3.75/0.99  --instantiation_flag                    true
% 3.75/0.99  --inst_sos_flag                         false
% 3.75/0.99  --inst_sos_phase                        true
% 3.75/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.99  --inst_lit_sel_side                     none
% 3.75/0.99  --inst_solver_per_active                1400
% 3.75/0.99  --inst_solver_calls_frac                1.
% 3.75/0.99  --inst_passive_queue_type               priority_queues
% 3.75/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.99  --inst_passive_queues_freq              [25;2]
% 3.75/0.99  --inst_dismatching                      true
% 3.75/0.99  --inst_eager_unprocessed_to_passive     true
% 3.75/0.99  --inst_prop_sim_given                   true
% 3.75/0.99  --inst_prop_sim_new                     false
% 3.75/0.99  --inst_subs_new                         false
% 3.75/0.99  --inst_eq_res_simp                      false
% 3.75/0.99  --inst_subs_given                       false
% 3.75/0.99  --inst_orphan_elimination               true
% 3.75/0.99  --inst_learning_loop_flag               true
% 3.75/0.99  --inst_learning_start                   3000
% 3.75/0.99  --inst_learning_factor                  2
% 3.75/0.99  --inst_start_prop_sim_after_learn       3
% 3.75/0.99  --inst_sel_renew                        solver
% 3.75/0.99  --inst_lit_activity_flag                true
% 3.75/0.99  --inst_restr_to_given                   false
% 3.75/0.99  --inst_activity_threshold               500
% 3.75/0.99  --inst_out_proof                        true
% 3.75/0.99  
% 3.75/0.99  ------ Resolution Options
% 3.75/0.99  
% 3.75/0.99  --resolution_flag                       false
% 3.75/0.99  --res_lit_sel                           adaptive
% 3.75/0.99  --res_lit_sel_side                      none
% 3.75/0.99  --res_ordering                          kbo
% 3.75/0.99  --res_to_prop_solver                    active
% 3.75/0.99  --res_prop_simpl_new                    false
% 3.75/0.99  --res_prop_simpl_given                  true
% 3.75/0.99  --res_passive_queue_type                priority_queues
% 3.75/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.99  --res_passive_queues_freq               [15;5]
% 3.75/0.99  --res_forward_subs                      full
% 3.75/0.99  --res_backward_subs                     full
% 3.75/0.99  --res_forward_subs_resolution           true
% 3.75/0.99  --res_backward_subs_resolution          true
% 3.75/0.99  --res_orphan_elimination                true
% 3.75/0.99  --res_time_limit                        2.
% 3.75/0.99  --res_out_proof                         true
% 3.75/0.99  
% 3.75/0.99  ------ Superposition Options
% 3.75/0.99  
% 3.75/0.99  --superposition_flag                    true
% 3.75/0.99  --sup_passive_queue_type                priority_queues
% 3.75/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.99  --demod_completeness_check              fast
% 3.75/0.99  --demod_use_ground                      true
% 3.75/0.99  --sup_to_prop_solver                    passive
% 3.75/0.99  --sup_prop_simpl_new                    true
% 3.75/0.99  --sup_prop_simpl_given                  true
% 3.75/0.99  --sup_fun_splitting                     false
% 3.75/0.99  --sup_smt_interval                      50000
% 3.75/0.99  
% 3.75/0.99  ------ Superposition Simplification Setup
% 3.75/0.99  
% 3.75/0.99  --sup_indices_passive                   []
% 3.75/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.99  --sup_full_bw                           [BwDemod]
% 3.75/0.99  --sup_immed_triv                        [TrivRules]
% 3.75/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.99  --sup_immed_bw_main                     []
% 3.75/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.99  
% 3.75/0.99  ------ Combination Options
% 3.75/0.99  
% 3.75/0.99  --comb_res_mult                         3
% 3.75/0.99  --comb_sup_mult                         2
% 3.75/0.99  --comb_inst_mult                        10
% 3.75/0.99  
% 3.75/0.99  ------ Debug Options
% 3.75/0.99  
% 3.75/0.99  --dbg_backtrace                         false
% 3.75/0.99  --dbg_dump_prop_clauses                 false
% 3.75/0.99  --dbg_dump_prop_clauses_file            -
% 3.75/0.99  --dbg_out_stat                          false
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  ------ Proving...
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  % SZS status Theorem for theBenchmark.p
% 3.75/0.99  
% 3.75/0.99   Resolution empty clause
% 3.75/0.99  
% 3.75/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.99  
% 3.75/0.99  fof(f16,axiom,(
% 3.75/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f48,plain,(
% 3.75/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.75/0.99    inference(nnf_transformation,[],[f16])).
% 3.75/0.99  
% 3.75/0.99  fof(f49,plain,(
% 3.75/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.75/0.99    inference(flattening,[],[f48])).
% 3.75/0.99  
% 3.75/0.99  fof(f82,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f49])).
% 3.75/0.99  
% 3.75/0.99  fof(f12,axiom,(
% 3.75/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f76,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f12])).
% 3.75/0.99  
% 3.75/0.99  fof(f13,axiom,(
% 3.75/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f77,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f13])).
% 3.75/0.99  
% 3.75/0.99  fof(f14,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f78,plain,(
% 3.75/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f14])).
% 3.75/0.99  
% 3.75/0.99  fof(f15,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f79,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f15])).
% 3.75/0.99  
% 3.75/0.99  fof(f110,plain,(
% 3.75/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f78,f79])).
% 3.75/0.99  
% 3.75/0.99  fof(f111,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f77,f110])).
% 3.75/0.99  
% 3.75/0.99  fof(f112,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f76,f111])).
% 3.75/0.99  
% 3.75/0.99  fof(f123,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f82,f112])).
% 3.75/0.99  
% 3.75/0.99  fof(f3,axiom,(
% 3.75/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f26,plain,(
% 3.75/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.75/0.99    inference(rectify,[],[f3])).
% 3.75/0.99  
% 3.75/0.99  fof(f66,plain,(
% 3.75/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.75/0.99    inference(cnf_transformation,[],[f26])).
% 3.75/0.99  
% 3.75/0.99  fof(f19,axiom,(
% 3.75/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f100,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.75/0.99    inference(cnf_transformation,[],[f19])).
% 3.75/0.99  
% 3.75/0.99  fof(f113,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.75/0.99    inference(definition_unfolding,[],[f100,f112])).
% 3.75/0.99  
% 3.75/0.99  fof(f115,plain,(
% 3.75/0.99    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.75/0.99    inference(definition_unfolding,[],[f66,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f21,axiom,(
% 3.75/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f34,plain,(
% 3.75/0.99    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 3.75/0.99    inference(ennf_transformation,[],[f21])).
% 3.75/0.99  
% 3.75/0.99  fof(f35,plain,(
% 3.75/0.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 3.75/0.99    inference(flattening,[],[f34])).
% 3.75/0.99  
% 3.75/0.99  fof(f103,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f35])).
% 3.75/0.99  
% 3.75/0.99  fof(f9,axiom,(
% 3.75/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f73,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f9])).
% 3.75/0.99  
% 3.75/0.99  fof(f5,axiom,(
% 3.75/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f69,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.75/0.99    inference(cnf_transformation,[],[f5])).
% 3.75/0.99  
% 3.75/0.99  fof(f114,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.75/0.99    inference(definition_unfolding,[],[f69,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f121,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f73,f114])).
% 3.75/0.99  
% 3.75/0.99  fof(f8,axiom,(
% 3.75/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f31,plain,(
% 3.75/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.75/0.99    inference(ennf_transformation,[],[f8])).
% 3.75/0.99  
% 3.75/0.99  fof(f72,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f31])).
% 3.75/0.99  
% 3.75/0.99  fof(f120,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f72,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f10,axiom,(
% 3.75/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f74,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f10])).
% 3.75/0.99  
% 3.75/0.99  fof(f122,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f74,f114])).
% 3.75/0.99  
% 3.75/0.99  fof(f1,axiom,(
% 3.75/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f42,plain,(
% 3.75/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.99    inference(nnf_transformation,[],[f1])).
% 3.75/0.99  
% 3.75/0.99  fof(f43,plain,(
% 3.75/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.99    inference(rectify,[],[f42])).
% 3.75/0.99  
% 3.75/0.99  fof(f44,plain,(
% 3.75/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f45,plain,(
% 3.75/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 3.75/0.99  
% 3.75/0.99  fof(f64,plain,(
% 3.75/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f45])).
% 3.75/0.99  
% 3.75/0.99  fof(f4,axiom,(
% 3.75/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f27,plain,(
% 3.75/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.75/0.99    inference(rectify,[],[f4])).
% 3.75/0.99  
% 3.75/0.99  fof(f28,plain,(
% 3.75/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.75/0.99    inference(ennf_transformation,[],[f27])).
% 3.75/0.99  
% 3.75/0.99  fof(f46,plain,(
% 3.75/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f47,plain,(
% 3.75/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f46])).
% 3.75/0.99  
% 3.75/0.99  fof(f68,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.75/0.99    inference(cnf_transformation,[],[f47])).
% 3.75/0.99  
% 3.75/0.99  fof(f116,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.75/0.99    inference(definition_unfolding,[],[f68,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f2,axiom,(
% 3.75/0.99    v1_xboole_0(k1_xboole_0)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f65,plain,(
% 3.75/0.99    v1_xboole_0(k1_xboole_0)),
% 3.75/0.99    inference(cnf_transformation,[],[f2])).
% 3.75/0.99  
% 3.75/0.99  fof(f11,axiom,(
% 3.75/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f32,plain,(
% 3.75/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.75/0.99    inference(ennf_transformation,[],[f11])).
% 3.75/0.99  
% 3.75/0.99  fof(f75,plain,(
% 3.75/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f32])).
% 3.75/0.99  
% 3.75/0.99  fof(f17,axiom,(
% 3.75/0.99    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f50,plain,(
% 3.75/0.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.75/0.99    inference(nnf_transformation,[],[f17])).
% 3.75/0.99  
% 3.75/0.99  fof(f51,plain,(
% 3.75/0.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.75/0.99    inference(flattening,[],[f50])).
% 3.75/0.99  
% 3.75/0.99  fof(f83,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f51])).
% 3.75/0.99  
% 3.75/0.99  fof(f128,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f83,f114,f112,f112])).
% 3.75/0.99  
% 3.75/0.99  fof(f18,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f33,plain,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 3.75/0.99    inference(ennf_transformation,[],[f18])).
% 3.75/0.99  
% 3.75/0.99  fof(f40,plain,(
% 3.75/0.99    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 3.75/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.75/0.99  
% 3.75/0.99  fof(f41,plain,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 3.75/0.99    inference(definition_folding,[],[f33,f40])).
% 3.75/0.99  
% 3.75/0.99  fof(f57,plain,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 3.75/0.99    inference(nnf_transformation,[],[f41])).
% 3.75/0.99  
% 3.75/0.99  fof(f98,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 3.75/0.99    inference(cnf_transformation,[],[f57])).
% 3.75/0.99  
% 3.75/0.99  fof(f130,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 3.75/0.99    inference(definition_unfolding,[],[f98,f79])).
% 3.75/0.99  
% 3.75/0.99  fof(f137,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 3.75/0.99    inference(equality_resolution,[],[f130])).
% 3.75/0.99  
% 3.75/0.99  fof(f52,plain,(
% 3.75/0.99    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 3.75/0.99    inference(nnf_transformation,[],[f40])).
% 3.75/0.99  
% 3.75/0.99  fof(f53,plain,(
% 3.75/0.99    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 3.75/0.99    inference(flattening,[],[f52])).
% 3.75/0.99  
% 3.75/0.99  fof(f54,plain,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 3.75/0.99    inference(rectify,[],[f53])).
% 3.75/0.99  
% 3.75/0.99  fof(f55,plain,(
% 3.75/0.99    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X0 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X0 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f56,plain,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK3(X0,X1,X2,X3,X4,X5) != X0 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X0 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 3.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 3.75/0.99  
% 3.75/0.99  fof(f87,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f56])).
% 3.75/0.99  
% 3.75/0.99  fof(f136,plain,(
% 3.75/0.99    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 3.75/0.99    inference(equality_resolution,[],[f87])).
% 3.75/0.99  
% 3.75/0.99  fof(f23,axiom,(
% 3.75/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f37,plain,(
% 3.75/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.99    inference(ennf_transformation,[],[f23])).
% 3.75/0.99  
% 3.75/0.99  fof(f38,plain,(
% 3.75/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.99    inference(flattening,[],[f37])).
% 3.75/0.99  
% 3.75/0.99  fof(f105,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f38])).
% 3.75/0.99  
% 3.75/0.99  fof(f22,axiom,(
% 3.75/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f36,plain,(
% 3.75/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.75/0.99    inference(ennf_transformation,[],[f22])).
% 3.75/0.99  
% 3.75/0.99  fof(f104,plain,(
% 3.75/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f36])).
% 3.75/0.99  
% 3.75/0.99  fof(f20,axiom,(
% 3.75/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f58,plain,(
% 3.75/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.75/0.99    inference(nnf_transformation,[],[f20])).
% 3.75/0.99  
% 3.75/0.99  fof(f102,plain,(
% 3.75/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f58])).
% 3.75/0.99  
% 3.75/0.99  fof(f7,axiom,(
% 3.75/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f29,plain,(
% 3.75/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.75/0.99    inference(ennf_transformation,[],[f7])).
% 3.75/0.99  
% 3.75/0.99  fof(f30,plain,(
% 3.75/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.75/0.99    inference(flattening,[],[f29])).
% 3.75/0.99  
% 3.75/0.99  fof(f71,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f30])).
% 3.75/0.99  
% 3.75/0.99  fof(f119,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f71,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f24,conjecture,(
% 3.75/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f25,negated_conjecture,(
% 3.75/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 3.75/0.99    inference(negated_conjecture,[],[f24])).
% 3.75/0.99  
% 3.75/0.99  fof(f39,plain,(
% 3.75/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.75/0.99    inference(ennf_transformation,[],[f25])).
% 3.75/0.99  
% 3.75/0.99  fof(f61,plain,(
% 3.75/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK6)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK6))) & v1_relat_1(sK6))) )),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f60,plain,(
% 3.75/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(sK5,X2)),k3_xboole_0(k5_relat_1(X0,sK5),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK5))) )),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f59,plain,(
% 3.75/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK4,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK4,X1),k5_relat_1(sK4,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK4))),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f62,plain,(
% 3.75/0.99    ((~r1_tarski(k5_relat_1(sK4,k3_xboole_0(sK5,sK6)),k3_xboole_0(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6))) & v1_relat_1(sK6)) & v1_relat_1(sK5)) & v1_relat_1(sK4)),
% 3.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f61,f60,f59])).
% 3.75/0.99  
% 3.75/0.99  fof(f109,plain,(
% 3.75/0.99    ~r1_tarski(k5_relat_1(sK4,k3_xboole_0(sK5,sK6)),k3_xboole_0(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))),
% 3.75/0.99    inference(cnf_transformation,[],[f62])).
% 3.75/0.99  
% 3.75/0.99  fof(f131,plain,(
% 3.75/0.99    ~r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6))))),
% 3.75/0.99    inference(definition_unfolding,[],[f109,f113,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f106,plain,(
% 3.75/0.99    v1_relat_1(sK4)),
% 3.75/0.99    inference(cnf_transformation,[],[f62])).
% 3.75/0.99  
% 3.75/0.99  fof(f107,plain,(
% 3.75/0.99    v1_relat_1(sK5)),
% 3.75/0.99    inference(cnf_transformation,[],[f62])).
% 3.75/0.99  
% 3.75/0.99  fof(f6,axiom,(
% 3.75/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.75/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f70,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f6])).
% 3.75/0.99  
% 3.75/0.99  fof(f118,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f70,f113])).
% 3.75/0.99  
% 3.75/0.99  fof(f108,plain,(
% 3.75/0.99    v1_relat_1(sK6)),
% 3.75/0.99    inference(cnf_transformation,[],[f62])).
% 3.75/0.99  
% 3.75/0.99  fof(f91,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X0 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f56])).
% 3.75/0.99  
% 3.75/0.99  fof(f132,plain,(
% 3.75/0.99    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X1,X2,X3,X4,X5)) )),
% 3.75/0.99    inference(equality_resolution,[],[f91])).
% 3.75/0.99  
% 3.75/0.99  cnf(c_12,plain,
% 3.75/0.99      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
% 3.75/0.99      | ~ r2_hidden(X0,X2)
% 3.75/0.99      | ~ r2_hidden(X1,X2) ),
% 3.75/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3368,plain,
% 3.75/0.99      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) = iProver_top
% 3.75/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.75/0.99      | r2_hidden(X1,X2) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3,plain,
% 3.75/0.99      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_34,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,X1)
% 3.75/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 3.75/0.99      | k1_xboole_0 = X0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3348,plain,
% 3.75/0.99      ( k1_xboole_0 = X0
% 3.75/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.75/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_5288,plain,
% 3.75/0.99      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.75/0.99      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
% 3.75/0.99      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3,c_3348]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_8351,plain,
% 3.75/0.99      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.75/0.99      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top
% 3.75/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3368,c_5288]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_9,plain,
% 3.75/0.99      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3371,plain,
% 3.75/0.99      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4028,plain,
% 3.75/0.99      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3,c_3371]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_8,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3372,plain,
% 3.75/0.99      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0
% 3.75/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_5126,plain,
% 3.75/0.99      ( k1_setfam_1(k4_enumset1(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),X0)) = k5_xboole_0(X0,X0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_4028,c_3372]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_10,plain,
% 3.75/0.99      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
% 3.75/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3370,plain,
% 3.75/0.99      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3843,plain,
% 3.75/0.99      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3,c_3370]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_0,plain,
% 3.75/0.99      ( r2_hidden(sK1(X0),X0) | v1_xboole_0(X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3379,plain,
% 3.75/0.99      ( r2_hidden(sK1(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4,plain,
% 3.75/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.75/0.99      | ~ r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 3.75/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3376,plain,
% 3.75/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.75/0.99      | r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_6452,plain,
% 3.75/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.75/0.99      | v1_xboole_0(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3379,c_3376]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_2,plain,
% 3.75/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3377,plain,
% 3.75/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11,plain,
% 3.75/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3369,plain,
% 3.75/0.99      ( X0 = X1
% 3.75/0.99      | v1_xboole_0(X1) != iProver_top
% 3.75/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4280,plain,
% 3.75/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3377,c_3369]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7860,plain,
% 3.75/0.99      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k1_xboole_0
% 3.75/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_6452,c_4280]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7988,plain,
% 3.75/0.99      ( k1_setfam_1(k4_enumset1(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),X0)) = k1_xboole_0 ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3843,c_7860]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11424,plain,
% 3.75/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.75/0.99      inference(light_normalisation,[status(thm)],[c_5126,c_7988]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_17,plain,
% 3.75/0.99      ( ~ r2_hidden(X0,X1)
% 3.75/0.99      | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),X1))) != k4_enumset1(X0,X0,X0,X0,X0,X2) ),
% 3.75/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3363,plain,
% 3.75/0.99      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1)
% 3.75/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_6644,plain,
% 3.75/0.99      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) != k4_enumset1(X0,X0,X0,X0,X0,X1)
% 3.75/0.99      | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3,c_3363]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_31,plain,
% 3.75/0.99      ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) ),
% 3.75/0.99      inference(cnf_transformation,[],[f137]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3349,plain,
% 3.75/0.99      ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_28,plain,
% 3.75/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 3.75/0.99      inference(cnf_transformation,[],[f136]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3352,plain,
% 3.75/0.99      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 3.75/0.99      | r2_hidden(X4,X5) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4456,plain,
% 3.75/0.99      ( r2_hidden(X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) = iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3349,c_3352]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_10512,plain,
% 3.75/0.99      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) != k4_enumset1(X0,X0,X0,X0,X0,X1) ),
% 3.75/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6644,c_4456]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11439,plain,
% 3.75/0.99      ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k1_xboole_0 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_11424,c_10512]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_12527,plain,
% 3.75/0.99      ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
% 3.75/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.75/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_8351,c_11439]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_36,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,X1)
% 3.75/0.99      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.75/0.99      | ~ v1_relat_1(X0)
% 3.75/0.99      | ~ v1_relat_1(X2)
% 3.75/0.99      | ~ v1_relat_1(X1) ),
% 3.75/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_35,plain,
% 3.75/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_32,plain,
% 3.75/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.75/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_215,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.75/0.99      | ~ r1_tarski(X0,X1)
% 3.75/0.99      | ~ v1_relat_1(X2)
% 3.75/0.99      | ~ v1_relat_1(X1) ),
% 3.75/0.99      inference(global_propositional_subsumption,
% 3.75/0.99                [status(thm)],
% 3.75/0.99                [c_36,c_35,c_32]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_216,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,X1)
% 3.75/0.99      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.75/0.99      | ~ v1_relat_1(X1)
% 3.75/0.99      | ~ v1_relat_1(X2) ),
% 3.75/0.99      inference(renaming,[status(thm)],[c_215]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3343,plain,
% 3.75/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.99      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
% 3.75/0.99      | v1_relat_1(X2) != iProver_top
% 3.75/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,X1)
% 3.75/0.99      | ~ r1_tarski(X0,X2)
% 3.75/0.99      | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
% 3.75/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3373,plain,
% 3.75/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.75/0.99      | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_37,negated_conjecture,
% 3.75/0.99      ( ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) ),
% 3.75/0.99      inference(cnf_transformation,[],[f131]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3347,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_6959,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) != iProver_top
% 3.75/0.99      | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5)) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3373,c_3347]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_40,negated_conjecture,
% 3.75/0.99      ( v1_relat_1(sK4) ),
% 3.75/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_41,plain,
% 3.75/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_39,negated_conjecture,
% 3.75/0.99      ( v1_relat_1(sK5) ),
% 3.75/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_42,plain,
% 3.75/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_44,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3833,plain,
% 3.75/0.99      ( ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6))
% 3.75/0.99      | ~ r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5))
% 3.75/0.99      | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3834,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) != iProver_top
% 3.75/0.99      | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5)) != iProver_top
% 3.75/0.99      | r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k1_setfam_1(k4_enumset1(k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK5),k5_relat_1(sK4,sK6)))) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_3833]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3658,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_relat_1(X0,X1))
% 3.75/0.99      | ~ r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1)
% 3.75/0.99      | ~ v1_relat_1(X1)
% 3.75/0.99      | ~ v1_relat_1(X0) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_216]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4535,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5))
% 3.75/0.99      | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5)
% 3.75/0.99      | ~ v1_relat_1(sK5)
% 3.75/0.99      | ~ v1_relat_1(sK4) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_3658]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4538,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK5)) = iProver_top
% 3.75/0.99      | r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5) != iProver_top
% 3.75/0.99      | v1_relat_1(sK5) != iProver_top
% 3.75/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_4535]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_6,plain,
% 3.75/0.99      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4881,plain,
% 3.75/0.99      ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4882,plain,
% 3.75/0.99      ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK5) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_4881]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7425,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) != iProver_top ),
% 3.75/0.99      inference(global_propositional_subsumption,
% 3.75/0.99                [status(thm)],
% 3.75/0.99                [c_6959,c_41,c_42,c_44,c_3834,c_4538,c_4882]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7430,plain,
% 3.75/0.99      ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6) != iProver_top
% 3.75/0.99      | v1_relat_1(sK6) != iProver_top
% 3.75/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3343,c_7425]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_38,negated_conjecture,
% 3.75/0.99      ( v1_relat_1(sK6) ),
% 3.75/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_43,plain,
% 3.75/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3951,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6))
% 3.75/0.99      | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6)
% 3.75/0.99      | ~ v1_relat_1(sK6)
% 3.75/0.99      | ~ v1_relat_1(sK4) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_216]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3952,plain,
% 3.75/0.99      ( r1_tarski(k5_relat_1(sK4,k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))),k5_relat_1(sK4,sK6)) = iProver_top
% 3.75/0.99      | r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6) != iProver_top
% 3.75/0.99      | v1_relat_1(sK6) != iProver_top
% 3.75/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_3951]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7433,plain,
% 3.75/0.99      ( r1_tarski(k1_setfam_1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),sK6) != iProver_top ),
% 3.75/0.99      inference(global_propositional_subsumption,
% 3.75/0.99                [status(thm)],
% 3.75/0.99                [c_7430,c_41,c_42,c_43,c_44,c_3834,c_3952,c_4538,c_4882]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_12537,plain,
% 3.75/0.99      ( r2_hidden(sK6,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) != iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_12527,c_7433]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_24,plain,
% 3.75/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X0,X5) ),
% 3.75/0.99      inference(cnf_transformation,[],[f132]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3356,plain,
% 3.75/0.99      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 3.75/0.99      | r2_hidden(X0,X5) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4989,plain,
% 3.75/0.99      ( r2_hidden(X0,k4_enumset1(X1,X1,X2,X3,X4,X0)) = iProver_top ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_3349,c_3356]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_12906,plain,
% 3.75/0.99      ( $false ),
% 3.75/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_12537,c_4989]) ).
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.99  
% 3.75/0.99  ------                               Statistics
% 3.75/0.99  
% 3.75/0.99  ------ General
% 3.75/0.99  
% 3.75/0.99  abstr_ref_over_cycles:                  0
% 3.75/0.99  abstr_ref_under_cycles:                 0
% 3.75/0.99  gc_basic_clause_elim:                   0
% 3.75/0.99  forced_gc_time:                         0
% 3.75/0.99  parsing_time:                           0.013
% 3.75/0.99  unif_index_cands_time:                  0.
% 3.75/0.99  unif_index_add_time:                    0.
% 3.75/0.99  orderings_time:                         0.
% 3.75/0.99  out_proof_time:                         0.012
% 3.75/0.99  total_time:                             0.424
% 3.75/0.99  num_of_symbols:                         50
% 3.75/0.99  num_of_terms:                           15393
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing
% 3.75/0.99  
% 3.75/0.99  num_of_splits:                          0
% 3.75/0.99  num_of_split_atoms:                     0
% 3.75/0.99  num_of_reused_defs:                     0
% 3.75/0.99  num_eq_ax_congr_red:                    47
% 3.75/0.99  num_of_sem_filtered_clauses:            1
% 3.75/0.99  num_of_subtypes:                        0
% 3.75/0.99  monotx_restored_types:                  0
% 3.75/0.99  sat_num_of_epr_types:                   0
% 3.75/0.99  sat_num_of_non_cyclic_types:            0
% 3.75/0.99  sat_guarded_non_collapsed_types:        0
% 3.75/0.99  num_pure_diseq_elim:                    0
% 3.75/0.99  simp_replaced_by:                       0
% 3.75/0.99  res_preprocessed:                       183
% 3.75/0.99  prep_upred:                             0
% 3.75/0.99  prep_unflattend:                        88
% 3.75/0.99  smt_new_axioms:                         0
% 3.75/0.99  pred_elim_cands:                        6
% 3.75/0.99  pred_elim:                              1
% 3.75/0.99  pred_elim_cl:                           2
% 3.75/0.99  pred_elim_cycles:                       5
% 3.75/0.99  merged_defs:                            2
% 3.75/0.99  merged_defs_ncl:                        0
% 3.75/0.99  bin_hyper_res:                          3
% 3.75/0.99  prep_cycles:                            4
% 3.75/0.99  pred_elim_time:                         0.026
% 3.75/0.99  splitting_time:                         0.
% 3.75/0.99  sem_filter_time:                        0.
% 3.75/0.99  monotx_time:                            0.001
% 3.75/0.99  subtype_inf_time:                       0.
% 3.75/0.99  
% 3.75/0.99  ------ Problem properties
% 3.75/0.99  
% 3.75/0.99  clauses:                                39
% 3.75/0.99  conjectures:                            4
% 3.75/0.99  epr:                                    13
% 3.75/0.99  horn:                                   33
% 3.75/0.99  ground:                                 5
% 3.75/0.99  unary:                                  10
% 3.75/0.99  binary:                                 15
% 3.75/0.99  lits:                                   91
% 3.75/0.99  lits_eq:                                23
% 3.75/0.99  fd_pure:                                0
% 3.75/0.99  fd_pseudo:                              0
% 3.75/0.99  fd_cond:                                1
% 3.75/0.99  fd_pseudo_cond:                         3
% 3.75/0.99  ac_symbols:                             0
% 3.75/0.99  
% 3.75/0.99  ------ Propositional Solver
% 3.75/0.99  
% 3.75/0.99  prop_solver_calls:                      28
% 3.75/0.99  prop_fast_solver_calls:                 1497
% 3.75/0.99  smt_solver_calls:                       0
% 3.75/0.99  smt_fast_solver_calls:                  0
% 3.75/0.99  prop_num_of_clauses:                    3993
% 3.75/0.99  prop_preprocess_simplified:             13529
% 3.75/0.99  prop_fo_subsumed:                       9
% 3.75/0.99  prop_solver_time:                       0.
% 3.75/0.99  smt_solver_time:                        0.
% 3.75/0.99  smt_fast_solver_time:                   0.
% 3.75/0.99  prop_fast_solver_time:                  0.
% 3.75/0.99  prop_unsat_core_time:                   0.
% 3.75/0.99  
% 3.75/0.99  ------ QBF
% 3.75/0.99  
% 3.75/0.99  qbf_q_res:                              0
% 3.75/0.99  qbf_num_tautologies:                    0
% 3.75/0.99  qbf_prep_cycles:                        0
% 3.75/0.99  
% 3.75/0.99  ------ BMC1
% 3.75/0.99  
% 3.75/0.99  bmc1_current_bound:                     -1
% 3.75/0.99  bmc1_last_solved_bound:                 -1
% 3.75/0.99  bmc1_unsat_core_size:                   -1
% 3.75/0.99  bmc1_unsat_core_parents_size:           -1
% 3.75/0.99  bmc1_merge_next_fun:                    0
% 3.75/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.75/0.99  
% 3.75/0.99  ------ Instantiation
% 3.75/0.99  
% 3.75/0.99  inst_num_of_clauses:                    1099
% 3.75/0.99  inst_num_in_passive:                    499
% 3.75/0.99  inst_num_in_active:                     389
% 3.75/0.99  inst_num_in_unprocessed:                211
% 3.75/0.99  inst_num_of_loops:                      470
% 3.75/0.99  inst_num_of_learning_restarts:          0
% 3.75/0.99  inst_num_moves_active_passive:          79
% 3.75/0.99  inst_lit_activity:                      0
% 3.75/0.99  inst_lit_activity_moves:                0
% 3.75/0.99  inst_num_tautologies:                   0
% 3.75/0.99  inst_num_prop_implied:                  0
% 3.75/0.99  inst_num_existing_simplified:           0
% 3.75/0.99  inst_num_eq_res_simplified:             0
% 3.75/0.99  inst_num_child_elim:                    0
% 3.75/0.99  inst_num_of_dismatching_blockings:      795
% 3.75/0.99  inst_num_of_non_proper_insts:           1501
% 3.75/0.99  inst_num_of_duplicates:                 0
% 3.75/0.99  inst_inst_num_from_inst_to_res:         0
% 3.75/0.99  inst_dismatching_checking_time:         0.
% 3.75/0.99  
% 3.75/0.99  ------ Resolution
% 3.75/0.99  
% 3.75/0.99  res_num_of_clauses:                     0
% 3.75/0.99  res_num_in_passive:                     0
% 3.75/0.99  res_num_in_active:                      0
% 3.75/0.99  res_num_of_loops:                       187
% 3.75/0.99  res_forward_subset_subsumed:            195
% 3.75/0.99  res_backward_subset_subsumed:           0
% 3.75/0.99  res_forward_subsumed:                   0
% 3.75/0.99  res_backward_subsumed:                  0
% 3.75/0.99  res_forward_subsumption_resolution:     0
% 3.75/0.99  res_backward_subsumption_resolution:    0
% 3.75/0.99  res_clause_to_clause_subsumption:       2100
% 3.75/0.99  res_orphan_elimination:                 0
% 3.75/0.99  res_tautology_del:                      39
% 3.75/0.99  res_num_eq_res_simplified:              0
% 3.75/0.99  res_num_sel_changes:                    0
% 3.75/0.99  res_moves_from_active_to_pass:          0
% 3.75/0.99  
% 3.75/0.99  ------ Superposition
% 3.75/0.99  
% 3.75/0.99  sup_time_total:                         0.
% 3.75/0.99  sup_time_generating:                    0.
% 3.75/0.99  sup_time_sim_full:                      0.
% 3.75/0.99  sup_time_sim_immed:                     0.
% 3.75/0.99  
% 3.75/0.99  sup_num_of_clauses:                     159
% 3.75/0.99  sup_num_in_active:                      77
% 3.75/0.99  sup_num_in_passive:                     82
% 3.75/0.99  sup_num_of_loops:                       93
% 3.75/0.99  sup_fw_superposition:                   117
% 3.75/0.99  sup_bw_superposition:                   127
% 3.75/0.99  sup_immediate_simplified:               37
% 3.75/0.99  sup_given_eliminated:                   1
% 3.75/0.99  comparisons_done:                       0
% 3.75/0.99  comparisons_avoided:                    0
% 3.75/0.99  
% 3.75/0.99  ------ Simplifications
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  sim_fw_subset_subsumed:                 10
% 3.75/0.99  sim_bw_subset_subsumed:                 3
% 3.75/0.99  sim_fw_subsumed:                        15
% 3.75/0.99  sim_bw_subsumed:                        0
% 3.75/0.99  sim_fw_subsumption_res:                 4
% 3.75/0.99  sim_bw_subsumption_res:                 0
% 3.75/0.99  sim_tautology_del:                      20
% 3.75/0.99  sim_eq_tautology_del:                   4
% 3.75/0.99  sim_eq_res_simp:                        1
% 3.75/0.99  sim_fw_demodulated:                     8
% 3.75/0.99  sim_bw_demodulated:                     17
% 3.75/0.99  sim_light_normalised:                   11
% 3.75/0.99  sim_joinable_taut:                      0
% 3.75/0.99  sim_joinable_simp:                      0
% 3.75/0.99  sim_ac_normalised:                      0
% 3.75/0.99  sim_smt_subsumption:                    0
% 3.75/0.99  
%------------------------------------------------------------------------------
