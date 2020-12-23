%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:33 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 422 expanded)
%              Number of clauses        :   63 (  76 expanded)
%              Number of leaves         :   27 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  489 (1061 expanded)
%              Number of equality atoms :  236 ( 572 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f97])).

fof(f99,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f98])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f69,f99])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f87,f99])).

fof(f102,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f100])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f101,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f100])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f101,f99,f99])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f59,f101])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f106,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f61,f101])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f30,f37])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f85,f66])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f114])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
            & sK1(X0,X1,X2,X3,X4,X5) != X1
            & sK1(X0,X1,X2,X3,X4,X5) != X2
            & sK1(X0,X1,X2,X3,X4,X5) != X3
            & sK1(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK1(X0,X1,X2,X3,X4,X5) = X0
          | sK1(X0,X1,X2,X3,X4,X5) = X1
          | sK1(X0,X1,X2,X3,X4,X5) = X2
          | sK1(X0,X1,X2,X3,X4,X5) = X3
          | sK1(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
              & sK1(X0,X1,X2,X3,X4,X5) != X1
              & sK1(X0,X1,X2,X3,X4,X5) != X2
              & sK1(X0,X1,X2,X3,X4,X5) != X3
              & sK1(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK1(X0,X1,X2,X3,X4,X5) = X0
            | sK1(X0,X1,X2,X3,X4,X5) = X1
            | sK1(X0,X1,X2,X3,X4,X5) = X2
            | sK1(X0,X1,X2,X3,X4,X5) = X3
            | sK1(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f74,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f120,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f74])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f100])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK4)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK4)))
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(X0,sK3),k5_relat_1(X0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f52,f51,f50])).

fof(f96,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
    inference(definition_unfolding,[],[f96,f100,f100])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f57,f100])).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X1,X2,X3,X4,X5) ) ),
    inference(equality_resolution,[],[f78])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3241,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3221,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4767,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3221])).

cnf(c_6907,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3241,c_4767])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),X1))) != k4_enumset1(X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3236,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8338,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) != k4_enumset1(X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3236])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3245,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3918,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3245])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3244,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5630,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) != iProver_top
    | v1_xboole_0(k5_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3918,c_3244])).

cnf(c_6,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3243,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3709,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3243])).

cnf(c_6327,plain,
    ( v1_xboole_0(k5_xboole_0(X0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5630,c_3709])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3248,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3242,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4163,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3248,c_3242])).

cnf(c_6334,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6327,c_4163])).

cnf(c_8339,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8338,c_6334])).

cnf(c_27,plain,
    ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3222,plain,
    ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3225,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X4,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4257,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3222,c_3225])).

cnf(c_8793,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8339,c_4257])).

cnf(c_9690,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6907,c_8793])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_191,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_31,c_28])).

cnf(c_192,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_3216,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3246,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_33,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3220,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6051,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) != iProver_top
    | r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_3220])).

cnf(c_6096,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3216,c_6051])).

cnf(c_36,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_39,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6240,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6096,c_37,c_39])).

cnf(c_6246,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3216,c_6240])).

cnf(c_35,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_38,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6249,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6246,c_37,c_38])).

cnf(c_2,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3247,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6255,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6249,c_3247])).

cnf(c_9699,plain,
    ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9690,c_6255])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X0,X5) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3229,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X0,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4606,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X2,X3,X4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3222,c_3229])).

cnf(c_10002,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9699,c_4606])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:13:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.88/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.97  
% 3.88/0.97  ------  iProver source info
% 3.88/0.97  
% 3.88/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.97  git: non_committed_changes: false
% 3.88/0.97  git: last_make_outside_of_git: false
% 3.88/0.97  
% 3.88/0.97  ------ 
% 3.88/0.97  ------ Parsing...
% 3.88/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.97  
% 3.88/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.88/0.97  
% 3.88/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.97  
% 3.88/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.97  ------ Proving...
% 3.88/0.97  ------ Problem Properties 
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  clauses                                 35
% 3.88/0.97  conjectures                             4
% 3.88/0.97  EPR                                     13
% 3.88/0.97  Horn                                    31
% 3.88/0.97  unary                                   10
% 3.88/0.97  binary                                  10
% 3.88/0.97  lits                                    84
% 3.88/0.97  lits eq                                 22
% 3.88/0.97  fd_pure                                 0
% 3.88/0.97  fd_pseudo                               0
% 3.88/0.97  fd_cond                                 1
% 3.88/0.97  fd_pseudo_cond                          3
% 3.88/0.97  AC symbols                              0
% 3.88/0.97  
% 3.88/0.97  ------ Input Options Time Limit: Unbounded
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  ------ 
% 3.88/0.97  Current options:
% 3.88/0.97  ------ 
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  ------ Proving...
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  % SZS status Theorem for theBenchmark.p
% 3.88/0.97  
% 3.88/0.97   Resolution empty clause
% 3.88/0.97  
% 3.88/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  fof(f14,axiom,(
% 3.88/0.97    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f39,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.88/0.97    inference(nnf_transformation,[],[f14])).
% 3.88/0.97  
% 3.88/0.97  fof(f40,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.88/0.97    inference(flattening,[],[f39])).
% 3.88/0.97  
% 3.88/0.97  fof(f69,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f40])).
% 3.88/0.97  
% 3.88/0.97  fof(f10,axiom,(
% 3.88/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f63,plain,(
% 3.88/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f10])).
% 3.88/0.97  
% 3.88/0.97  fof(f11,axiom,(
% 3.88/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f64,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f11])).
% 3.88/0.97  
% 3.88/0.97  fof(f12,axiom,(
% 3.88/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f65,plain,(
% 3.88/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f12])).
% 3.88/0.97  
% 3.88/0.97  fof(f13,axiom,(
% 3.88/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f66,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f13])).
% 3.88/0.97  
% 3.88/0.97  fof(f97,plain,(
% 3.88/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f65,f66])).
% 3.88/0.97  
% 3.88/0.97  fof(f98,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f64,f97])).
% 3.88/0.97  
% 3.88/0.97  fof(f99,plain,(
% 3.88/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f63,f98])).
% 3.88/0.97  
% 3.88/0.97  fof(f107,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f69,f99])).
% 3.88/0.97  
% 3.88/0.97  fof(f2,axiom,(
% 3.88/0.97    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f24,plain,(
% 3.88/0.97    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.88/0.97    inference(rectify,[],[f2])).
% 3.88/0.97  
% 3.88/0.97  fof(f55,plain,(
% 3.88/0.97    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.88/0.97    inference(cnf_transformation,[],[f24])).
% 3.88/0.97  
% 3.88/0.97  fof(f17,axiom,(
% 3.88/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f87,plain,(
% 3.88/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.88/0.97    inference(cnf_transformation,[],[f17])).
% 3.88/0.97  
% 3.88/0.97  fof(f100,plain,(
% 3.88/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.88/0.97    inference(definition_unfolding,[],[f87,f99])).
% 3.88/0.97  
% 3.88/0.97  fof(f102,plain,(
% 3.88/0.97    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.88/0.97    inference(definition_unfolding,[],[f55,f100])).
% 3.88/0.97  
% 3.88/0.97  fof(f19,axiom,(
% 3.88/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f31,plain,(
% 3.88/0.97    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 3.88/0.97    inference(ennf_transformation,[],[f19])).
% 3.88/0.97  
% 3.88/0.97  fof(f32,plain,(
% 3.88/0.97    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 3.88/0.97    inference(flattening,[],[f31])).
% 3.88/0.97  
% 3.88/0.97  fof(f90,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f32])).
% 3.88/0.97  
% 3.88/0.97  fof(f15,axiom,(
% 3.88/0.97    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f41,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.88/0.97    inference(nnf_transformation,[],[f15])).
% 3.88/0.97  
% 3.88/0.97  fof(f42,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.88/0.97    inference(flattening,[],[f41])).
% 3.88/0.97  
% 3.88/0.97  fof(f70,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f42])).
% 3.88/0.97  
% 3.88/0.97  fof(f3,axiom,(
% 3.88/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f56,plain,(
% 3.88/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.88/0.97    inference(cnf_transformation,[],[f3])).
% 3.88/0.97  
% 3.88/0.97  fof(f101,plain,(
% 3.88/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.88/0.97    inference(definition_unfolding,[],[f56,f100])).
% 3.88/0.97  
% 3.88/0.97  fof(f112,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f70,f101,f99,f99])).
% 3.88/0.97  
% 3.88/0.97  fof(f6,axiom,(
% 3.88/0.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f59,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f6])).
% 3.88/0.97  
% 3.88/0.97  fof(f105,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f59,f101])).
% 3.88/0.97  
% 3.88/0.97  fof(f7,axiom,(
% 3.88/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f27,plain,(
% 3.88/0.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.88/0.97    inference(ennf_transformation,[],[f7])).
% 3.88/0.97  
% 3.88/0.97  fof(f28,plain,(
% 3.88/0.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.88/0.97    inference(flattening,[],[f27])).
% 3.88/0.97  
% 3.88/0.97  fof(f60,plain,(
% 3.88/0.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f28])).
% 3.88/0.97  
% 3.88/0.97  fof(f8,axiom,(
% 3.88/0.97    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f61,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f8])).
% 3.88/0.97  
% 3.88/0.97  fof(f106,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1)) )),
% 3.88/0.97    inference(definition_unfolding,[],[f61,f101])).
% 3.88/0.97  
% 3.88/0.97  fof(f1,axiom,(
% 3.88/0.97    v1_xboole_0(k1_xboole_0)),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f54,plain,(
% 3.88/0.97    v1_xboole_0(k1_xboole_0)),
% 3.88/0.97    inference(cnf_transformation,[],[f1])).
% 3.88/0.97  
% 3.88/0.97  fof(f9,axiom,(
% 3.88/0.97    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f29,plain,(
% 3.88/0.97    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.88/0.97    inference(ennf_transformation,[],[f9])).
% 3.88/0.97  
% 3.88/0.97  fof(f62,plain,(
% 3.88/0.97    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f29])).
% 3.88/0.97  
% 3.88/0.97  fof(f16,axiom,(
% 3.88/0.97    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 3.88/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f30,plain,(
% 3.88/0.97    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 3.88/0.97    inference(ennf_transformation,[],[f16])).
% 3.88/0.97  
% 3.88/0.97  fof(f37,plain,(
% 3.88/0.97    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 3.88/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.88/0.97  
% 3.88/0.97  fof(f38,plain,(
% 3.88/0.97    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 3.88/0.97    inference(definition_folding,[],[f30,f37])).
% 3.88/0.97  
% 3.88/0.97  fof(f48,plain,(
% 3.88/0.97    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 3.88/0.97    inference(nnf_transformation,[],[f38])).
% 3.88/0.97  
% 3.88/0.97  fof(f85,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 3.88/0.97    inference(cnf_transformation,[],[f48])).
% 3.88/0.97  
% 3.88/0.97  fof(f114,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 3.88/0.97    inference(definition_unfolding,[],[f85,f66])).
% 3.88/0.97  
% 3.88/0.97  fof(f121,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 3.88/0.97    inference(equality_resolution,[],[f114])).
% 3.88/0.97  
% 3.88/0.97  fof(f43,plain,(
% 3.88/0.97    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 3.88/0.97    inference(nnf_transformation,[],[f37])).
% 3.88/0.97  
% 3.88/0.97  fof(f44,plain,(
% 3.88/0.97    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 3.88/0.97    inference(flattening,[],[f43])).
% 3.88/0.97  
% 3.88/0.97  fof(f45,plain,(
% 3.88/0.97    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 3.88/0.97    inference(rectify,[],[f44])).
% 3.88/0.98  
% 3.88/0.98  fof(f46,plain,(
% 3.88/0.98    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5))))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f47,plain,(
% 3.88/0.98    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.88/0.98  
% 3.88/0.98  fof(f74,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f47])).
% 3.88/0.98  
% 3.88/0.98  fof(f120,plain,(
% 3.88/0.98    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 3.88/0.98    inference(equality_resolution,[],[f74])).
% 3.88/0.98  
% 3.88/0.98  fof(f21,axiom,(
% 3.88/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f34,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f21])).
% 3.88/0.98  
% 3.88/0.98  fof(f35,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.88/0.98    inference(flattening,[],[f34])).
% 3.88/0.98  
% 3.88/0.98  fof(f92,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f35])).
% 3.88/0.98  
% 3.88/0.98  fof(f20,axiom,(
% 3.88/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f33,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f20])).
% 3.88/0.98  
% 3.88/0.98  fof(f91,plain,(
% 3.88/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f33])).
% 3.88/0.98  
% 3.88/0.98  fof(f18,axiom,(
% 3.88/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f49,plain,(
% 3.88/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.88/0.98    inference(nnf_transformation,[],[f18])).
% 3.88/0.98  
% 3.88/0.98  fof(f89,plain,(
% 3.88/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f5,axiom,(
% 3.88/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f25,plain,(
% 3.88/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.88/0.98    inference(ennf_transformation,[],[f5])).
% 3.88/0.98  
% 3.88/0.98  fof(f26,plain,(
% 3.88/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.88/0.98    inference(flattening,[],[f25])).
% 3.88/0.98  
% 3.88/0.98  fof(f58,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f26])).
% 3.88/0.98  
% 3.88/0.98  fof(f104,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(definition_unfolding,[],[f58,f100])).
% 3.88/0.98  
% 3.88/0.98  fof(f22,conjecture,(
% 3.88/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f23,negated_conjecture,(
% 3.88/0.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 3.88/0.98    inference(negated_conjecture,[],[f22])).
% 3.88/0.98  
% 3.88/0.98  fof(f36,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f23])).
% 3.88/0.98  
% 3.88/0.98  fof(f52,plain,(
% 3.88/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK4)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK4))) & v1_relat_1(sK4))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f51,plain,(
% 3.88/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(X0,sK3),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK3))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f50,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f53,plain,(
% 3.88/0.98    ((~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) & v1_relat_1(sK4)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f52,f51,f50])).
% 3.88/0.98  
% 3.88/0.98  fof(f96,plain,(
% 3.88/0.98    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))),
% 3.88/0.98    inference(cnf_transformation,[],[f53])).
% 3.88/0.98  
% 3.88/0.98  fof(f115,plain,(
% 3.88/0.98    ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))))),
% 3.88/0.98    inference(definition_unfolding,[],[f96,f100,f100])).
% 3.88/0.98  
% 3.88/0.98  fof(f93,plain,(
% 3.88/0.98    v1_relat_1(sK2)),
% 3.88/0.98    inference(cnf_transformation,[],[f53])).
% 3.88/0.98  
% 3.88/0.98  fof(f95,plain,(
% 3.88/0.98    v1_relat_1(sK4)),
% 3.88/0.98    inference(cnf_transformation,[],[f53])).
% 3.88/0.98  
% 3.88/0.98  fof(f94,plain,(
% 3.88/0.98    v1_relat_1(sK3)),
% 3.88/0.98    inference(cnf_transformation,[],[f53])).
% 3.88/0.98  
% 3.88/0.98  fof(f4,axiom,(
% 3.88/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f57,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f4])).
% 3.88/0.98  
% 3.88/0.98  fof(f103,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.88/0.98    inference(definition_unfolding,[],[f57,f100])).
% 3.88/0.98  
% 3.88/0.98  fof(f78,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X0 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f47])).
% 3.88/0.98  
% 3.88/0.98  fof(f116,plain,(
% 3.88/0.98    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X1,X2,X3,X4,X5)) )),
% 3.88/0.98    inference(equality_resolution,[],[f78])).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,X1)
% 3.88/0.98      | ~ r2_hidden(X2,X1)
% 3.88/0.98      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3241,plain,
% 3.88/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.88/0.98      | r2_hidden(X2,X1) != iProver_top
% 3.88/0.98      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1,plain,
% 3.88/0.98      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_30,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1)
% 3.88/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 3.88/0.98      | k1_xboole_0 = X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3221,plain,
% 3.88/0.98      ( k1_xboole_0 = X0
% 3.88/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4767,plain,
% 3.88/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.88/0.98      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1,c_3221]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6907,plain,
% 3.88/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.88/0.98      | r2_hidden(X0,X1) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3241,c_4767]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_13,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,X1)
% 3.88/0.98      | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),k4_enumset1(X0,X0,X0,X0,X0,X2),X1))) != k4_enumset1(X0,X0,X0,X0,X0,X2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3236,plain,
% 3.88/0.98      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) != k4_enumset1(X0,X0,X0,X0,X0,X1)
% 3.88/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8338,plain,
% 3.88/0.98      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) != k4_enumset1(X0,X0,X0,X0,X0,X1)
% 3.88/0.98      | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1,c_3236]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4,plain,
% 3.88/0.98      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3245,plain,
% 3.88/0.98      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3918,plain,
% 3.88/0.98      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1,c_3245]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5,plain,
% 3.88/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3244,plain,
% 3.88/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.88/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5630,plain,
% 3.88/0.98      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) != iProver_top
% 3.88/0.98      | v1_xboole_0(k5_xboole_0(X0,X0)) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3918,c_3244]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6,plain,
% 3.88/0.98      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3243,plain,
% 3.88/0.98      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3709,plain,
% 3.88/0.98      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1,c_3243]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6327,plain,
% 3.88/0.98      ( v1_xboole_0(k5_xboole_0(X0,X0)) = iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5630,c_3709]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_0,plain,
% 3.88/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3248,plain,
% 3.88/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7,plain,
% 3.88/0.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.88/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3242,plain,
% 3.88/0.98      ( X0 = X1
% 3.88/0.98      | v1_xboole_0(X0) != iProver_top
% 3.88/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4163,plain,
% 3.88/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3248,c_3242]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6334,plain,
% 3.88/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_6327,c_4163]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8339,plain,
% 3.88/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k1_xboole_0
% 3.88/0.98      | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_8338,c_6334]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_27,plain,
% 3.88/0.98      ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3222,plain,
% 3.88/0.98      ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_24,plain,
% 3.88/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 3.88/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3225,plain,
% 3.88/0.98      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 3.88/0.98      | r2_hidden(X4,X5) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4257,plain,
% 3.88/0.98      ( r2_hidden(X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3222,c_3225]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8793,plain,
% 3.88/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k1_xboole_0 ),
% 3.88/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_8339,c_4257]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_9690,plain,
% 3.88/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 3.88/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6907,c_8793]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_32,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1)
% 3.88/0.98      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.88/0.98      | ~ v1_relat_1(X0)
% 3.88/0.98      | ~ v1_relat_1(X1)
% 3.88/0.98      | ~ v1_relat_1(X2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_31,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_28,plain,
% 3.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_191,plain,
% 3.88/0.98      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.88/0.98      | ~ r1_tarski(X0,X1)
% 3.88/0.98      | ~ v1_relat_1(X1)
% 3.88/0.98      | ~ v1_relat_1(X2) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_32,c_31,c_28]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_192,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1)
% 3.88/0.98      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.88/0.98      | ~ v1_relat_1(X1)
% 3.88/0.98      | ~ v1_relat_1(X2) ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_191]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3216,plain,
% 3.88/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.98      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
% 3.88/0.98      | v1_relat_1(X1) != iProver_top
% 3.88/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1)
% 3.88/0.98      | ~ r1_tarski(X0,X2)
% 3.88/0.98      | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
% 3.88/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3246,plain,
% 3.88/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.88/0.98      | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_33,negated_conjecture,
% 3.88/0.98      ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
% 3.88/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3220,plain,
% 3.88/0.98      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6051,plain,
% 3.88/0.98      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) != iProver_top
% 3.88/0.98      | r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3246,c_3220]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6096,plain,
% 3.88/0.98      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
% 3.88/0.98      | v1_relat_1(sK4) != iProver_top
% 3.88/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3216,c_6051]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_36,negated_conjecture,
% 3.88/0.98      ( v1_relat_1(sK2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_37,plain,
% 3.88/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_34,negated_conjecture,
% 3.88/0.98      ( v1_relat_1(sK4) ),
% 3.88/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_39,plain,
% 3.88/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6240,plain,
% 3.88/0.98      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_6096,c_37,c_39]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6246,plain,
% 3.88/0.98      ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top
% 3.88/0.98      | v1_relat_1(sK3) != iProver_top
% 3.88/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3216,c_6240]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_35,negated_conjecture,
% 3.88/0.98      ( v1_relat_1(sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_38,plain,
% 3.88/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6249,plain,
% 3.88/0.98      ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
% 3.88/0.98      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_6246,c_37,c_38]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2,plain,
% 3.88/0.98      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3247,plain,
% 3.88/0.98      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6255,plain,
% 3.88/0.98      ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
% 3.88/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6249,c_3247]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_9699,plain,
% 3.88/0.98      ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_9690,c_6255]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_20,plain,
% 3.88/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X0,X5) ),
% 3.88/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3229,plain,
% 3.88/0.98      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 3.88/0.98      | r2_hidden(X0,X5) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4606,plain,
% 3.88/0.98      ( r2_hidden(X0,k4_enumset1(X1,X1,X2,X3,X4,X0)) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3222,c_3229]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_10002,plain,
% 3.88/0.98      ( $false ),
% 3.88/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_9699,c_4606]) ).
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  ------                               Statistics
% 3.88/0.98  
% 3.88/0.98  ------ Selected
% 3.88/0.98  
% 3.88/0.98  total_time:                             0.49
% 3.88/0.98  
%------------------------------------------------------------------------------
