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
% DateTime   : Thu Dec  3 11:43:33 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 407 expanded)
%              Number of clauses        :   59 (  72 expanded)
%              Number of leaves         :   27 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  471 (1032 expanded)
%              Number of equality atoms :  230 ( 555 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f96,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f95])).

fof(f97,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f96])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f68,f97])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f85,f97])).

fof(f101,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f98])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f98])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f97])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f69,f99,f100])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f58,f99])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f105,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f60,f99])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f83,f65])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f112])).

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f72,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f118,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f72])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f90,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f98])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK4)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK4)))
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f52,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f51,f50,f49])).

fof(f94,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f113,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
    inference(definition_unfolding,[],[f94,f98,f98])).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f56,f98])).

fof(f76,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X1,X2,X3,X4,X5) ) ),
    inference(equality_resolution,[],[f76])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3364,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3345,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6025,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3345])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0)))) != X1 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3360,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1)))) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6468,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0)) != k4_enumset1(X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3360])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3366,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3964,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3366])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_464,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_1])).

cnf(c_3338,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_3980,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3964,c_3338])).

cnf(c_6,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3365,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3680,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3365])).

cnf(c_4150,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3980,c_3680])).

cnf(c_6469,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k1_xboole_0
    | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6468,c_4150])).

cnf(c_25,plain,
    ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3346,plain,
    ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3349,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X4,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4364,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3346,c_3349])).

cnf(c_6807,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6469,c_4364])).

cnf(c_7306,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6025,c_6807])).

cnf(c_7315,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_7306])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_183,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_29,c_26])).

cnf(c_184,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_3340,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3367,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3344,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6818,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) != iProver_top
    | r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_3344])).

cnf(c_7196,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_6818])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_35,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7978,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7196,c_35,c_37])).

cnf(c_7984,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_7978])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_36,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7987,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
    | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7984,c_35,c_36])).

cnf(c_2,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3368,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7993,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7987,c_3368])).

cnf(c_8252,plain,
    ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7315,c_7993])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X0,X5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3353,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X0,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4878,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X2,X3,X4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3346,c_3353])).

cnf(c_8291,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8252,c_4878])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.81/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/1.00  
% 2.81/1.00  ------  iProver source info
% 2.81/1.00  
% 2.81/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.81/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/1.00  git: non_committed_changes: false
% 2.81/1.00  git: last_make_outside_of_git: false
% 2.81/1.00  
% 2.81/1.00  ------ 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options
% 2.81/1.00  
% 2.81/1.00  --out_options                           all
% 2.81/1.00  --tptp_safe_out                         true
% 2.81/1.00  --problem_path                          ""
% 2.81/1.00  --include_path                          ""
% 2.81/1.00  --clausifier                            res/vclausify_rel
% 2.81/1.00  --clausifier_options                    --mode clausify
% 2.81/1.00  --stdin                                 false
% 2.81/1.00  --stats_out                             all
% 2.81/1.00  
% 2.81/1.00  ------ General Options
% 2.81/1.00  
% 2.81/1.00  --fof                                   false
% 2.81/1.00  --time_out_real                         305.
% 2.81/1.00  --time_out_virtual                      -1.
% 2.81/1.00  --symbol_type_check                     false
% 2.81/1.00  --clausify_out                          false
% 2.81/1.00  --sig_cnt_out                           false
% 2.81/1.00  --trig_cnt_out                          false
% 2.81/1.00  --trig_cnt_out_tolerance                1.
% 2.81/1.00  --trig_cnt_out_sk_spl                   false
% 2.81/1.00  --abstr_cl_out                          false
% 2.81/1.00  
% 2.81/1.00  ------ Global Options
% 2.81/1.00  
% 2.81/1.00  --schedule                              default
% 2.81/1.00  --add_important_lit                     false
% 2.81/1.00  --prop_solver_per_cl                    1000
% 2.81/1.00  --min_unsat_core                        false
% 2.81/1.00  --soft_assumptions                      false
% 2.81/1.00  --soft_lemma_size                       3
% 2.81/1.00  --prop_impl_unit_size                   0
% 2.81/1.00  --prop_impl_unit                        []
% 2.81/1.00  --share_sel_clauses                     true
% 2.81/1.00  --reset_solvers                         false
% 2.81/1.00  --bc_imp_inh                            [conj_cone]
% 2.81/1.00  --conj_cone_tolerance                   3.
% 2.81/1.00  --extra_neg_conj                        none
% 2.81/1.00  --large_theory_mode                     true
% 2.81/1.00  --prolific_symb_bound                   200
% 2.81/1.00  --lt_threshold                          2000
% 2.81/1.00  --clause_weak_htbl                      true
% 2.81/1.00  --gc_record_bc_elim                     false
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing Options
% 2.81/1.00  
% 2.81/1.00  --preprocessing_flag                    true
% 2.81/1.00  --time_out_prep_mult                    0.1
% 2.81/1.00  --splitting_mode                        input
% 2.81/1.00  --splitting_grd                         true
% 2.81/1.00  --splitting_cvd                         false
% 2.81/1.00  --splitting_cvd_svl                     false
% 2.81/1.00  --splitting_nvd                         32
% 2.81/1.00  --sub_typing                            true
% 2.81/1.00  --prep_gs_sim                           true
% 2.81/1.00  --prep_unflatten                        true
% 2.81/1.00  --prep_res_sim                          true
% 2.81/1.00  --prep_upred                            true
% 2.81/1.00  --prep_sem_filter                       exhaustive
% 2.81/1.00  --prep_sem_filter_out                   false
% 2.81/1.00  --pred_elim                             true
% 2.81/1.00  --res_sim_input                         true
% 2.81/1.00  --eq_ax_congr_red                       true
% 2.81/1.00  --pure_diseq_elim                       true
% 2.81/1.00  --brand_transform                       false
% 2.81/1.00  --non_eq_to_eq                          false
% 2.81/1.00  --prep_def_merge                        true
% 2.81/1.00  --prep_def_merge_prop_impl              false
% 2.81/1.00  --prep_def_merge_mbd                    true
% 2.81/1.00  --prep_def_merge_tr_red                 false
% 2.81/1.00  --prep_def_merge_tr_cl                  false
% 2.81/1.00  --smt_preprocessing                     true
% 2.81/1.00  --smt_ac_axioms                         fast
% 2.81/1.00  --preprocessed_out                      false
% 2.81/1.00  --preprocessed_stats                    false
% 2.81/1.00  
% 2.81/1.00  ------ Abstraction refinement Options
% 2.81/1.00  
% 2.81/1.00  --abstr_ref                             []
% 2.81/1.00  --abstr_ref_prep                        false
% 2.81/1.00  --abstr_ref_until_sat                   false
% 2.81/1.00  --abstr_ref_sig_restrict                funpre
% 2.81/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/1.00  --abstr_ref_under                       []
% 2.81/1.00  
% 2.81/1.00  ------ SAT Options
% 2.81/1.00  
% 2.81/1.00  --sat_mode                              false
% 2.81/1.00  --sat_fm_restart_options                ""
% 2.81/1.00  --sat_gr_def                            false
% 2.81/1.00  --sat_epr_types                         true
% 2.81/1.00  --sat_non_cyclic_types                  false
% 2.81/1.00  --sat_finite_models                     false
% 2.81/1.00  --sat_fm_lemmas                         false
% 2.81/1.00  --sat_fm_prep                           false
% 2.81/1.00  --sat_fm_uc_incr                        true
% 2.81/1.00  --sat_out_model                         small
% 2.81/1.00  --sat_out_clauses                       false
% 2.81/1.00  
% 2.81/1.00  ------ QBF Options
% 2.81/1.00  
% 2.81/1.00  --qbf_mode                              false
% 2.81/1.00  --qbf_elim_univ                         false
% 2.81/1.00  --qbf_dom_inst                          none
% 2.81/1.00  --qbf_dom_pre_inst                      false
% 2.81/1.00  --qbf_sk_in                             false
% 2.81/1.00  --qbf_pred_elim                         true
% 2.81/1.00  --qbf_split                             512
% 2.81/1.00  
% 2.81/1.00  ------ BMC1 Options
% 2.81/1.00  
% 2.81/1.00  --bmc1_incremental                      false
% 2.81/1.00  --bmc1_axioms                           reachable_all
% 2.81/1.00  --bmc1_min_bound                        0
% 2.81/1.00  --bmc1_max_bound                        -1
% 2.81/1.00  --bmc1_max_bound_default                -1
% 2.81/1.00  --bmc1_symbol_reachability              true
% 2.81/1.00  --bmc1_property_lemmas                  false
% 2.81/1.00  --bmc1_k_induction                      false
% 2.81/1.00  --bmc1_non_equiv_states                 false
% 2.81/1.00  --bmc1_deadlock                         false
% 2.81/1.00  --bmc1_ucm                              false
% 2.81/1.00  --bmc1_add_unsat_core                   none
% 2.81/1.00  --bmc1_unsat_core_children              false
% 2.81/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/1.00  --bmc1_out_stat                         full
% 2.81/1.00  --bmc1_ground_init                      false
% 2.81/1.00  --bmc1_pre_inst_next_state              false
% 2.81/1.00  --bmc1_pre_inst_state                   false
% 2.81/1.00  --bmc1_pre_inst_reach_state             false
% 2.81/1.00  --bmc1_out_unsat_core                   false
% 2.81/1.00  --bmc1_aig_witness_out                  false
% 2.81/1.00  --bmc1_verbose                          false
% 2.81/1.00  --bmc1_dump_clauses_tptp                false
% 2.81/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.81/1.00  --bmc1_dump_file                        -
% 2.81/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.81/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.81/1.00  --bmc1_ucm_extend_mode                  1
% 2.81/1.00  --bmc1_ucm_init_mode                    2
% 2.81/1.00  --bmc1_ucm_cone_mode                    none
% 2.81/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.81/1.00  --bmc1_ucm_relax_model                  4
% 2.81/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.81/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/1.00  --bmc1_ucm_layered_model                none
% 2.81/1.01  --bmc1_ucm_max_lemma_size               10
% 2.81/1.01  
% 2.81/1.01  ------ AIG Options
% 2.81/1.01  
% 2.81/1.01  --aig_mode                              false
% 2.81/1.01  
% 2.81/1.01  ------ Instantiation Options
% 2.81/1.01  
% 2.81/1.01  --instantiation_flag                    true
% 2.81/1.01  --inst_sos_flag                         false
% 2.81/1.01  --inst_sos_phase                        true
% 2.81/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/1.01  --inst_lit_sel_side                     num_symb
% 2.81/1.01  --inst_solver_per_active                1400
% 2.81/1.01  --inst_solver_calls_frac                1.
% 2.81/1.01  --inst_passive_queue_type               priority_queues
% 2.81/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/1.01  --inst_passive_queues_freq              [25;2]
% 2.81/1.01  --inst_dismatching                      true
% 2.81/1.01  --inst_eager_unprocessed_to_passive     true
% 2.81/1.01  --inst_prop_sim_given                   true
% 2.81/1.01  --inst_prop_sim_new                     false
% 2.81/1.01  --inst_subs_new                         false
% 2.81/1.01  --inst_eq_res_simp                      false
% 2.81/1.01  --inst_subs_given                       false
% 2.81/1.01  --inst_orphan_elimination               true
% 2.81/1.01  --inst_learning_loop_flag               true
% 2.81/1.01  --inst_learning_start                   3000
% 2.81/1.01  --inst_learning_factor                  2
% 2.81/1.01  --inst_start_prop_sim_after_learn       3
% 2.81/1.01  --inst_sel_renew                        solver
% 2.81/1.01  --inst_lit_activity_flag                true
% 2.81/1.01  --inst_restr_to_given                   false
% 2.81/1.01  --inst_activity_threshold               500
% 2.81/1.01  --inst_out_proof                        true
% 2.81/1.01  
% 2.81/1.01  ------ Resolution Options
% 2.81/1.01  
% 2.81/1.01  --resolution_flag                       true
% 2.81/1.01  --res_lit_sel                           adaptive
% 2.81/1.01  --res_lit_sel_side                      none
% 2.81/1.01  --res_ordering                          kbo
% 2.81/1.01  --res_to_prop_solver                    active
% 2.81/1.01  --res_prop_simpl_new                    false
% 2.81/1.01  --res_prop_simpl_given                  true
% 2.81/1.01  --res_passive_queue_type                priority_queues
% 2.81/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/1.01  --res_passive_queues_freq               [15;5]
% 2.81/1.01  --res_forward_subs                      full
% 2.81/1.01  --res_backward_subs                     full
% 2.81/1.01  --res_forward_subs_resolution           true
% 2.81/1.01  --res_backward_subs_resolution          true
% 2.81/1.01  --res_orphan_elimination                true
% 2.81/1.01  --res_time_limit                        2.
% 2.81/1.01  --res_out_proof                         true
% 2.81/1.01  
% 2.81/1.01  ------ Superposition Options
% 2.81/1.01  
% 2.81/1.01  --superposition_flag                    true
% 2.81/1.01  --sup_passive_queue_type                priority_queues
% 2.81/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.81/1.01  --demod_completeness_check              fast
% 2.81/1.01  --demod_use_ground                      true
% 2.81/1.01  --sup_to_prop_solver                    passive
% 2.81/1.01  --sup_prop_simpl_new                    true
% 2.81/1.01  --sup_prop_simpl_given                  true
% 2.81/1.01  --sup_fun_splitting                     false
% 2.81/1.01  --sup_smt_interval                      50000
% 2.81/1.01  
% 2.81/1.01  ------ Superposition Simplification Setup
% 2.81/1.01  
% 2.81/1.01  --sup_indices_passive                   []
% 2.81/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.01  --sup_full_bw                           [BwDemod]
% 2.81/1.01  --sup_immed_triv                        [TrivRules]
% 2.81/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.01  --sup_immed_bw_main                     []
% 2.81/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.01  
% 2.81/1.01  ------ Combination Options
% 2.81/1.01  
% 2.81/1.01  --comb_res_mult                         3
% 2.81/1.01  --comb_sup_mult                         2
% 2.81/1.01  --comb_inst_mult                        10
% 2.81/1.01  
% 2.81/1.01  ------ Debug Options
% 2.81/1.01  
% 2.81/1.01  --dbg_backtrace                         false
% 2.81/1.01  --dbg_dump_prop_clauses                 false
% 2.81/1.01  --dbg_dump_prop_clauses_file            -
% 2.81/1.01  --dbg_out_stat                          false
% 2.81/1.01  ------ Parsing...
% 2.81/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/1.01  
% 2.81/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.81/1.01  
% 2.81/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/1.01  
% 2.81/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/1.01  ------ Proving...
% 2.81/1.01  ------ Problem Properties 
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  clauses                                 32
% 2.81/1.01  conjectures                             4
% 2.81/1.01  EPR                                     11
% 2.81/1.01  Horn                                    28
% 2.81/1.01  unary                                   9
% 2.81/1.01  binary                                  10
% 2.81/1.01  lits                                    77
% 2.81/1.01  lits eq                                 21
% 2.81/1.01  fd_pure                                 0
% 2.81/1.01  fd_pseudo                               0
% 2.81/1.01  fd_cond                                 2
% 2.81/1.01  fd_pseudo_cond                          2
% 2.81/1.01  AC symbols                              0
% 2.81/1.01  
% 2.81/1.01  ------ Schedule dynamic 5 is on 
% 2.81/1.01  
% 2.81/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  ------ 
% 2.81/1.01  Current options:
% 2.81/1.01  ------ 
% 2.81/1.01  
% 2.81/1.01  ------ Input Options
% 2.81/1.01  
% 2.81/1.01  --out_options                           all
% 2.81/1.01  --tptp_safe_out                         true
% 2.81/1.01  --problem_path                          ""
% 2.81/1.01  --include_path                          ""
% 2.81/1.01  --clausifier                            res/vclausify_rel
% 2.81/1.01  --clausifier_options                    --mode clausify
% 2.81/1.01  --stdin                                 false
% 2.81/1.01  --stats_out                             all
% 2.81/1.01  
% 2.81/1.01  ------ General Options
% 2.81/1.01  
% 2.81/1.01  --fof                                   false
% 2.81/1.01  --time_out_real                         305.
% 2.81/1.01  --time_out_virtual                      -1.
% 2.81/1.01  --symbol_type_check                     false
% 2.81/1.01  --clausify_out                          false
% 2.81/1.01  --sig_cnt_out                           false
% 2.81/1.01  --trig_cnt_out                          false
% 2.81/1.01  --trig_cnt_out_tolerance                1.
% 2.81/1.01  --trig_cnt_out_sk_spl                   false
% 2.81/1.01  --abstr_cl_out                          false
% 2.81/1.01  
% 2.81/1.01  ------ Global Options
% 2.81/1.01  
% 2.81/1.01  --schedule                              default
% 2.81/1.01  --add_important_lit                     false
% 2.81/1.01  --prop_solver_per_cl                    1000
% 2.81/1.01  --min_unsat_core                        false
% 2.81/1.01  --soft_assumptions                      false
% 2.81/1.01  --soft_lemma_size                       3
% 2.81/1.01  --prop_impl_unit_size                   0
% 2.81/1.01  --prop_impl_unit                        []
% 2.81/1.01  --share_sel_clauses                     true
% 2.81/1.01  --reset_solvers                         false
% 2.81/1.01  --bc_imp_inh                            [conj_cone]
% 2.81/1.01  --conj_cone_tolerance                   3.
% 2.81/1.01  --extra_neg_conj                        none
% 2.81/1.01  --large_theory_mode                     true
% 2.81/1.01  --prolific_symb_bound                   200
% 2.81/1.01  --lt_threshold                          2000
% 2.81/1.01  --clause_weak_htbl                      true
% 2.81/1.01  --gc_record_bc_elim                     false
% 2.81/1.01  
% 2.81/1.01  ------ Preprocessing Options
% 2.81/1.01  
% 2.81/1.01  --preprocessing_flag                    true
% 2.81/1.01  --time_out_prep_mult                    0.1
% 2.81/1.01  --splitting_mode                        input
% 2.81/1.01  --splitting_grd                         true
% 2.81/1.01  --splitting_cvd                         false
% 2.81/1.01  --splitting_cvd_svl                     false
% 2.81/1.01  --splitting_nvd                         32
% 2.81/1.01  --sub_typing                            true
% 2.81/1.01  --prep_gs_sim                           true
% 2.81/1.01  --prep_unflatten                        true
% 2.81/1.01  --prep_res_sim                          true
% 2.81/1.01  --prep_upred                            true
% 2.81/1.01  --prep_sem_filter                       exhaustive
% 2.81/1.01  --prep_sem_filter_out                   false
% 2.81/1.01  --pred_elim                             true
% 2.81/1.01  --res_sim_input                         true
% 2.81/1.01  --eq_ax_congr_red                       true
% 2.81/1.01  --pure_diseq_elim                       true
% 2.81/1.01  --brand_transform                       false
% 2.81/1.01  --non_eq_to_eq                          false
% 2.81/1.01  --prep_def_merge                        true
% 2.81/1.01  --prep_def_merge_prop_impl              false
% 2.81/1.01  --prep_def_merge_mbd                    true
% 2.81/1.01  --prep_def_merge_tr_red                 false
% 2.81/1.01  --prep_def_merge_tr_cl                  false
% 2.81/1.01  --smt_preprocessing                     true
% 2.81/1.01  --smt_ac_axioms                         fast
% 2.81/1.01  --preprocessed_out                      false
% 2.81/1.01  --preprocessed_stats                    false
% 2.81/1.01  
% 2.81/1.01  ------ Abstraction refinement Options
% 2.81/1.01  
% 2.81/1.01  --abstr_ref                             []
% 2.81/1.01  --abstr_ref_prep                        false
% 2.81/1.01  --abstr_ref_until_sat                   false
% 2.81/1.01  --abstr_ref_sig_restrict                funpre
% 2.81/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/1.01  --abstr_ref_under                       []
% 2.81/1.01  
% 2.81/1.01  ------ SAT Options
% 2.81/1.01  
% 2.81/1.01  --sat_mode                              false
% 2.81/1.01  --sat_fm_restart_options                ""
% 2.81/1.01  --sat_gr_def                            false
% 2.81/1.01  --sat_epr_types                         true
% 2.81/1.01  --sat_non_cyclic_types                  false
% 2.81/1.01  --sat_finite_models                     false
% 2.81/1.01  --sat_fm_lemmas                         false
% 2.81/1.01  --sat_fm_prep                           false
% 2.81/1.01  --sat_fm_uc_incr                        true
% 2.81/1.01  --sat_out_model                         small
% 2.81/1.01  --sat_out_clauses                       false
% 2.81/1.01  
% 2.81/1.01  ------ QBF Options
% 2.81/1.01  
% 2.81/1.01  --qbf_mode                              false
% 2.81/1.01  --qbf_elim_univ                         false
% 2.81/1.01  --qbf_dom_inst                          none
% 2.81/1.01  --qbf_dom_pre_inst                      false
% 2.81/1.01  --qbf_sk_in                             false
% 2.81/1.01  --qbf_pred_elim                         true
% 2.81/1.01  --qbf_split                             512
% 2.81/1.01  
% 2.81/1.01  ------ BMC1 Options
% 2.81/1.01  
% 2.81/1.01  --bmc1_incremental                      false
% 2.81/1.01  --bmc1_axioms                           reachable_all
% 2.81/1.01  --bmc1_min_bound                        0
% 2.81/1.01  --bmc1_max_bound                        -1
% 2.81/1.01  --bmc1_max_bound_default                -1
% 2.81/1.01  --bmc1_symbol_reachability              true
% 2.81/1.01  --bmc1_property_lemmas                  false
% 2.81/1.01  --bmc1_k_induction                      false
% 2.81/1.01  --bmc1_non_equiv_states                 false
% 2.81/1.01  --bmc1_deadlock                         false
% 2.81/1.01  --bmc1_ucm                              false
% 2.81/1.01  --bmc1_add_unsat_core                   none
% 2.81/1.01  --bmc1_unsat_core_children              false
% 2.81/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/1.01  --bmc1_out_stat                         full
% 2.81/1.01  --bmc1_ground_init                      false
% 2.81/1.01  --bmc1_pre_inst_next_state              false
% 2.81/1.01  --bmc1_pre_inst_state                   false
% 2.81/1.01  --bmc1_pre_inst_reach_state             false
% 2.81/1.01  --bmc1_out_unsat_core                   false
% 2.81/1.01  --bmc1_aig_witness_out                  false
% 2.81/1.01  --bmc1_verbose                          false
% 2.81/1.01  --bmc1_dump_clauses_tptp                false
% 2.81/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.81/1.01  --bmc1_dump_file                        -
% 2.81/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.81/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.81/1.01  --bmc1_ucm_extend_mode                  1
% 2.81/1.01  --bmc1_ucm_init_mode                    2
% 2.81/1.01  --bmc1_ucm_cone_mode                    none
% 2.81/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.81/1.01  --bmc1_ucm_relax_model                  4
% 2.81/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.81/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/1.01  --bmc1_ucm_layered_model                none
% 2.81/1.01  --bmc1_ucm_max_lemma_size               10
% 2.81/1.01  
% 2.81/1.01  ------ AIG Options
% 2.81/1.01  
% 2.81/1.01  --aig_mode                              false
% 2.81/1.01  
% 2.81/1.01  ------ Instantiation Options
% 2.81/1.01  
% 2.81/1.01  --instantiation_flag                    true
% 2.81/1.01  --inst_sos_flag                         false
% 2.81/1.01  --inst_sos_phase                        true
% 2.81/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/1.01  --inst_lit_sel_side                     none
% 2.81/1.01  --inst_solver_per_active                1400
% 2.81/1.01  --inst_solver_calls_frac                1.
% 2.81/1.01  --inst_passive_queue_type               priority_queues
% 2.81/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/1.01  --inst_passive_queues_freq              [25;2]
% 2.81/1.01  --inst_dismatching                      true
% 2.81/1.01  --inst_eager_unprocessed_to_passive     true
% 2.81/1.01  --inst_prop_sim_given                   true
% 2.81/1.01  --inst_prop_sim_new                     false
% 2.81/1.01  --inst_subs_new                         false
% 2.81/1.01  --inst_eq_res_simp                      false
% 2.81/1.01  --inst_subs_given                       false
% 2.81/1.01  --inst_orphan_elimination               true
% 2.81/1.01  --inst_learning_loop_flag               true
% 2.81/1.01  --inst_learning_start                   3000
% 2.81/1.01  --inst_learning_factor                  2
% 2.81/1.01  --inst_start_prop_sim_after_learn       3
% 2.81/1.01  --inst_sel_renew                        solver
% 2.81/1.01  --inst_lit_activity_flag                true
% 2.81/1.01  --inst_restr_to_given                   false
% 2.81/1.01  --inst_activity_threshold               500
% 2.81/1.01  --inst_out_proof                        true
% 2.81/1.01  
% 2.81/1.01  ------ Resolution Options
% 2.81/1.01  
% 2.81/1.01  --resolution_flag                       false
% 2.81/1.01  --res_lit_sel                           adaptive
% 2.81/1.01  --res_lit_sel_side                      none
% 2.81/1.01  --res_ordering                          kbo
% 2.81/1.01  --res_to_prop_solver                    active
% 2.81/1.01  --res_prop_simpl_new                    false
% 2.81/1.01  --res_prop_simpl_given                  true
% 2.81/1.01  --res_passive_queue_type                priority_queues
% 2.81/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/1.01  --res_passive_queues_freq               [15;5]
% 2.81/1.01  --res_forward_subs                      full
% 2.81/1.01  --res_backward_subs                     full
% 2.81/1.01  --res_forward_subs_resolution           true
% 2.81/1.01  --res_backward_subs_resolution          true
% 2.81/1.01  --res_orphan_elimination                true
% 2.81/1.01  --res_time_limit                        2.
% 2.81/1.01  --res_out_proof                         true
% 2.81/1.01  
% 2.81/1.01  ------ Superposition Options
% 2.81/1.01  
% 2.81/1.01  --superposition_flag                    true
% 2.81/1.01  --sup_passive_queue_type                priority_queues
% 2.81/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.81/1.01  --demod_completeness_check              fast
% 2.81/1.01  --demod_use_ground                      true
% 2.81/1.01  --sup_to_prop_solver                    passive
% 2.81/1.01  --sup_prop_simpl_new                    true
% 2.81/1.01  --sup_prop_simpl_given                  true
% 2.81/1.01  --sup_fun_splitting                     false
% 2.81/1.01  --sup_smt_interval                      50000
% 2.81/1.01  
% 2.81/1.01  ------ Superposition Simplification Setup
% 2.81/1.01  
% 2.81/1.01  --sup_indices_passive                   []
% 2.81/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.01  --sup_full_bw                           [BwDemod]
% 2.81/1.01  --sup_immed_triv                        [TrivRules]
% 2.81/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.01  --sup_immed_bw_main                     []
% 2.81/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.01  
% 2.81/1.01  ------ Combination Options
% 2.81/1.01  
% 2.81/1.01  --comb_res_mult                         3
% 2.81/1.01  --comb_sup_mult                         2
% 2.81/1.01  --comb_inst_mult                        10
% 2.81/1.01  
% 2.81/1.01  ------ Debug Options
% 2.81/1.01  
% 2.81/1.01  --dbg_backtrace                         false
% 2.81/1.01  --dbg_dump_prop_clauses                 false
% 2.81/1.01  --dbg_dump_prop_clauses_file            -
% 2.81/1.01  --dbg_out_stat                          false
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  ------ Proving...
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  % SZS status Theorem for theBenchmark.p
% 2.81/1.01  
% 2.81/1.01   Resolution empty clause
% 2.81/1.01  
% 2.81/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/1.01  
% 2.81/1.01  fof(f14,axiom,(
% 2.81/1.01    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f39,plain,(
% 2.81/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.81/1.01    inference(nnf_transformation,[],[f14])).
% 2.81/1.01  
% 2.81/1.01  fof(f40,plain,(
% 2.81/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.81/1.01    inference(flattening,[],[f39])).
% 2.81/1.01  
% 2.81/1.01  fof(f68,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f40])).
% 2.81/1.01  
% 2.81/1.01  fof(f10,axiom,(
% 2.81/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f62,plain,(
% 2.81/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f10])).
% 2.81/1.01  
% 2.81/1.01  fof(f11,axiom,(
% 2.81/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f63,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f11])).
% 2.81/1.01  
% 2.81/1.01  fof(f12,axiom,(
% 2.81/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f64,plain,(
% 2.81/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f12])).
% 2.81/1.01  
% 2.81/1.01  fof(f13,axiom,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f65,plain,(
% 2.81/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f13])).
% 2.81/1.01  
% 2.81/1.01  fof(f95,plain,(
% 2.81/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f64,f65])).
% 2.81/1.01  
% 2.81/1.01  fof(f96,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f63,f95])).
% 2.81/1.01  
% 2.81/1.01  fof(f97,plain,(
% 2.81/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f62,f96])).
% 2.81/1.01  
% 2.81/1.01  fof(f106,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f68,f97])).
% 2.81/1.01  
% 2.81/1.01  fof(f1,axiom,(
% 2.81/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f24,plain,(
% 2.81/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.81/1.01    inference(rectify,[],[f1])).
% 2.81/1.01  
% 2.81/1.01  fof(f53,plain,(
% 2.81/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.81/1.01    inference(cnf_transformation,[],[f24])).
% 2.81/1.01  
% 2.81/1.01  fof(f17,axiom,(
% 2.81/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f85,plain,(
% 2.81/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.81/1.01    inference(cnf_transformation,[],[f17])).
% 2.81/1.01  
% 2.81/1.01  fof(f98,plain,(
% 2.81/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.81/1.01    inference(definition_unfolding,[],[f85,f97])).
% 2.81/1.01  
% 2.81/1.01  fof(f101,plain,(
% 2.81/1.01    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.81/1.01    inference(definition_unfolding,[],[f53,f98])).
% 2.81/1.01  
% 2.81/1.01  fof(f19,axiom,(
% 2.81/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f31,plain,(
% 2.81/1.01    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.81/1.01    inference(ennf_transformation,[],[f19])).
% 2.81/1.01  
% 2.81/1.01  fof(f32,plain,(
% 2.81/1.01    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.81/1.01    inference(flattening,[],[f31])).
% 2.81/1.01  
% 2.81/1.01  fof(f88,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f32])).
% 2.81/1.01  
% 2.81/1.01  fof(f15,axiom,(
% 2.81/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f41,plain,(
% 2.81/1.01    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.81/1.01    inference(nnf_transformation,[],[f15])).
% 2.81/1.01  
% 2.81/1.01  fof(f69,plain,(
% 2.81/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 2.81/1.01    inference(cnf_transformation,[],[f41])).
% 2.81/1.01  
% 2.81/1.01  fof(f3,axiom,(
% 2.81/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f55,plain,(
% 2.81/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.81/1.01    inference(cnf_transformation,[],[f3])).
% 2.81/1.01  
% 2.81/1.01  fof(f99,plain,(
% 2.81/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 2.81/1.01    inference(definition_unfolding,[],[f55,f98])).
% 2.81/1.01  
% 2.81/1.01  fof(f9,axiom,(
% 2.81/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f61,plain,(
% 2.81/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f9])).
% 2.81/1.01  
% 2.81/1.01  fof(f100,plain,(
% 2.81/1.01    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f61,f97])).
% 2.81/1.01  
% 2.81/1.01  fof(f110,plain,(
% 2.81/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1)))) != X0) )),
% 2.81/1.01    inference(definition_unfolding,[],[f69,f99,f100])).
% 2.81/1.01  
% 2.81/1.01  fof(f6,axiom,(
% 2.81/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f58,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f6])).
% 2.81/1.01  
% 2.81/1.01  fof(f104,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f58,f99])).
% 2.81/1.01  
% 2.81/1.01  fof(f7,axiom,(
% 2.81/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f28,plain,(
% 2.81/1.01    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.81/1.01    inference(ennf_transformation,[],[f7])).
% 2.81/1.01  
% 2.81/1.01  fof(f29,plain,(
% 2.81/1.01    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.81/1.01    inference(flattening,[],[f28])).
% 2.81/1.01  
% 2.81/1.01  fof(f59,plain,(
% 2.81/1.01    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f29])).
% 2.81/1.01  
% 2.81/1.01  fof(f2,axiom,(
% 2.81/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f25,plain,(
% 2.81/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.81/1.01    inference(ennf_transformation,[],[f2])).
% 2.81/1.01  
% 2.81/1.01  fof(f54,plain,(
% 2.81/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f25])).
% 2.81/1.01  
% 2.81/1.01  fof(f8,axiom,(
% 2.81/1.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f60,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f8])).
% 2.81/1.01  
% 2.81/1.01  fof(f105,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f60,f99])).
% 2.81/1.01  
% 2.81/1.01  fof(f16,axiom,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f30,plain,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 2.81/1.01    inference(ennf_transformation,[],[f16])).
% 2.81/1.01  
% 2.81/1.01  fof(f37,plain,(
% 2.81/1.01    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 2.81/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.81/1.01  
% 2.81/1.01  fof(f38,plain,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 2.81/1.01    inference(definition_folding,[],[f30,f37])).
% 2.81/1.01  
% 2.81/1.01  fof(f47,plain,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 2.81/1.01    inference(nnf_transformation,[],[f38])).
% 2.81/1.01  
% 2.81/1.01  fof(f83,plain,(
% 2.81/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 2.81/1.01    inference(cnf_transformation,[],[f47])).
% 2.81/1.01  
% 2.81/1.01  fof(f112,plain,(
% 2.81/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 2.81/1.01    inference(definition_unfolding,[],[f83,f65])).
% 2.81/1.01  
% 2.81/1.01  fof(f119,plain,(
% 2.81/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 2.81/1.01    inference(equality_resolution,[],[f112])).
% 2.81/1.01  
% 2.81/1.01  fof(f42,plain,(
% 2.81/1.01    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 2.81/1.01    inference(nnf_transformation,[],[f37])).
% 2.81/1.01  
% 2.81/1.01  fof(f43,plain,(
% 2.81/1.01    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 2.81/1.01    inference(flattening,[],[f42])).
% 2.81/1.01  
% 2.81/1.01  fof(f44,plain,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 2.81/1.01    inference(rectify,[],[f43])).
% 2.81/1.01  
% 2.81/1.01  fof(f45,plain,(
% 2.81/1.01    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5))))),
% 2.81/1.01    introduced(choice_axiom,[])).
% 2.81/1.01  
% 2.81/1.01  fof(f46,plain,(
% 2.81/1.01    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 2.81/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 2.81/1.01  
% 2.81/1.01  fof(f72,plain,(
% 2.81/1.01    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f46])).
% 2.81/1.01  
% 2.81/1.01  fof(f118,plain,(
% 2.81/1.01    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 2.81/1.01    inference(equality_resolution,[],[f72])).
% 2.81/1.01  
% 2.81/1.01  fof(f21,axiom,(
% 2.81/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f34,plain,(
% 2.81/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.81/1.01    inference(ennf_transformation,[],[f21])).
% 2.81/1.01  
% 2.81/1.01  fof(f35,plain,(
% 2.81/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.81/1.01    inference(flattening,[],[f34])).
% 2.81/1.01  
% 2.81/1.01  fof(f90,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f35])).
% 2.81/1.01  
% 2.81/1.01  fof(f20,axiom,(
% 2.81/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f33,plain,(
% 2.81/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.81/1.01    inference(ennf_transformation,[],[f20])).
% 2.81/1.01  
% 2.81/1.01  fof(f89,plain,(
% 2.81/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f33])).
% 2.81/1.01  
% 2.81/1.01  fof(f18,axiom,(
% 2.81/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f48,plain,(
% 2.81/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.81/1.01    inference(nnf_transformation,[],[f18])).
% 2.81/1.01  
% 2.81/1.01  fof(f87,plain,(
% 2.81/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f48])).
% 2.81/1.01  
% 2.81/1.01  fof(f5,axiom,(
% 2.81/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f26,plain,(
% 2.81/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.81/1.01    inference(ennf_transformation,[],[f5])).
% 2.81/1.01  
% 2.81/1.01  fof(f27,plain,(
% 2.81/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.81/1.01    inference(flattening,[],[f26])).
% 2.81/1.01  
% 2.81/1.01  fof(f57,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f27])).
% 2.81/1.01  
% 2.81/1.01  fof(f103,plain,(
% 2.81/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f57,f98])).
% 2.81/1.01  
% 2.81/1.01  fof(f22,conjecture,(
% 2.81/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f23,negated_conjecture,(
% 2.81/1.01    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 2.81/1.01    inference(negated_conjecture,[],[f22])).
% 2.81/1.01  
% 2.81/1.01  fof(f36,plain,(
% 2.81/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.81/1.01    inference(ennf_transformation,[],[f23])).
% 2.81/1.01  
% 2.81/1.01  fof(f51,plain,(
% 2.81/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK4)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK4))) & v1_relat_1(sK4))) )),
% 2.81/1.01    introduced(choice_axiom,[])).
% 2.81/1.01  
% 2.81/1.01  fof(f50,plain,(
% 2.81/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(X0,sK3),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK3))) )),
% 2.81/1.01    introduced(choice_axiom,[])).
% 2.81/1.01  
% 2.81/1.01  fof(f49,plain,(
% 2.81/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 2.81/1.01    introduced(choice_axiom,[])).
% 2.81/1.01  
% 2.81/1.01  fof(f52,plain,(
% 2.81/1.01    ((~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) & v1_relat_1(sK4)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 2.81/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f51,f50,f49])).
% 2.81/1.01  
% 2.81/1.01  fof(f94,plain,(
% 2.81/1.01    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))),
% 2.81/1.01    inference(cnf_transformation,[],[f52])).
% 2.81/1.01  
% 2.81/1.01  fof(f113,plain,(
% 2.81/1.01    ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))))),
% 2.81/1.01    inference(definition_unfolding,[],[f94,f98,f98])).
% 2.81/1.01  
% 2.81/1.01  fof(f91,plain,(
% 2.81/1.01    v1_relat_1(sK2)),
% 2.81/1.01    inference(cnf_transformation,[],[f52])).
% 2.81/1.01  
% 2.81/1.01  fof(f93,plain,(
% 2.81/1.01    v1_relat_1(sK4)),
% 2.81/1.01    inference(cnf_transformation,[],[f52])).
% 2.81/1.01  
% 2.81/1.01  fof(f92,plain,(
% 2.81/1.01    v1_relat_1(sK3)),
% 2.81/1.01    inference(cnf_transformation,[],[f52])).
% 2.81/1.01  
% 2.81/1.01  fof(f4,axiom,(
% 2.81/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.81/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.01  
% 2.81/1.01  fof(f56,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f4])).
% 2.81/1.01  
% 2.81/1.01  fof(f102,plain,(
% 2.81/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 2.81/1.01    inference(definition_unfolding,[],[f56,f98])).
% 2.81/1.01  
% 2.81/1.01  fof(f76,plain,(
% 2.81/1.01    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X0 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 2.81/1.01    inference(cnf_transformation,[],[f46])).
% 2.81/1.01  
% 2.81/1.01  fof(f114,plain,(
% 2.81/1.01    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X1,X2,X3,X4,X5)) )),
% 2.81/1.01    inference(equality_resolution,[],[f76])).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7,plain,
% 2.81/1.01      ( ~ r2_hidden(X0,X1)
% 2.81/1.01      | ~ r2_hidden(X2,X1)
% 2.81/1.01      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
% 2.81/1.01      inference(cnf_transformation,[],[f106]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3364,plain,
% 2.81/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.81/1.01      | r2_hidden(X2,X1) != iProver_top
% 2.81/1.01      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_0,plain,
% 2.81/1.01      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.81/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_28,plain,
% 2.81/1.01      ( ~ r1_tarski(X0,X1)
% 2.81/1.01      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.81/1.01      | k1_xboole_0 = X0 ),
% 2.81/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3345,plain,
% 2.81/1.01      ( k1_xboole_0 = X0
% 2.81/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_6025,plain,
% 2.81/1.01      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 2.81/1.01      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_0,c_3345]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_11,plain,
% 2.81/1.01      ( ~ r2_hidden(X0,X1)
% 2.81/1.01      | k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X0,X0,X0,X0,X0,X0)))) != X1 ),
% 2.81/1.01      inference(cnf_transformation,[],[f110]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3360,plain,
% 2.81/1.01      ( k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1)))) != X0
% 2.81/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_6468,plain,
% 2.81/1.01      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0)) != k4_enumset1(X0,X0,X0,X0,X0,X0)
% 2.81/1.01      | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_0,c_3360]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_4,plain,
% 2.81/1.01      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
% 2.81/1.01      inference(cnf_transformation,[],[f104]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3366,plain,
% 2.81/1.01      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3964,plain,
% 2.81/1.01      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_0,c_3366]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_5,plain,
% 2.81/1.01      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.81/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_1,plain,
% 2.81/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.81/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_464,plain,
% 2.81/1.01      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | k1_xboole_0 = X0 ),
% 2.81/1.01      inference(resolution,[status(thm)],[c_5,c_1]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3338,plain,
% 2.81/1.01      ( k1_xboole_0 = X0
% 2.81/1.01      | r1_xboole_0(X0,X1) != iProver_top
% 2.81/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3980,plain,
% 2.81/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0
% 2.81/1.01      | r1_xboole_0(k5_xboole_0(X0,X0),X0) != iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3964,c_3338]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_6,plain,
% 2.81/1.01      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
% 2.81/1.01      inference(cnf_transformation,[],[f105]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3365,plain,
% 2.81/1.01      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3680,plain,
% 2.81/1.01      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_0,c_3365]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_4150,plain,
% 2.81/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.81/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3980,c_3680]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_6469,plain,
% 2.81/1.01      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k1_xboole_0
% 2.81/1.01      | r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 2.81/1.01      inference(demodulation,[status(thm)],[c_6468,c_4150]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_25,plain,
% 2.81/1.01      ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) ),
% 2.81/1.01      inference(cnf_transformation,[],[f119]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3346,plain,
% 2.81/1.01      ( sP0(X0,X1,X2,X3,X4,k4_enumset1(X4,X4,X3,X2,X1,X0)) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_22,plain,
% 2.81/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 2.81/1.01      inference(cnf_transformation,[],[f118]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3349,plain,
% 2.81/1.01      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 2.81/1.01      | r2_hidden(X4,X5) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_4364,plain,
% 2.81/1.01      ( r2_hidden(X0,k4_enumset1(X0,X0,X1,X2,X3,X4)) = iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3346,c_3349]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_6807,plain,
% 2.81/1.01      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.81/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6469,c_4364]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7306,plain,
% 2.81/1.01      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 2.81/1.01      inference(global_propositional_subsumption,[status(thm)],[c_6025,c_6807]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7315,plain,
% 2.81/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3364,c_7306]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_30,plain,
% 2.81/1.01      ( ~ r1_tarski(X0,X1)
% 2.81/1.01      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 2.81/1.01      | ~ v1_relat_1(X0)
% 2.81/1.01      | ~ v1_relat_1(X1)
% 2.81/1.01      | ~ v1_relat_1(X2) ),
% 2.81/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_29,plain,
% 2.81/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.81/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_26,plain,
% 2.81/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.81/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_183,plain,
% 2.81/1.01      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 2.81/1.01      | ~ r1_tarski(X0,X1)
% 2.81/1.01      | ~ v1_relat_1(X1)
% 2.81/1.01      | ~ v1_relat_1(X2) ),
% 2.81/1.01      inference(global_propositional_subsumption,
% 2.81/1.01                [status(thm)],
% 2.81/1.01                [c_30,c_29,c_26]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_184,plain,
% 2.81/1.01      ( ~ r1_tarski(X0,X1)
% 2.81/1.01      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 2.81/1.01      | ~ v1_relat_1(X1)
% 2.81/1.01      | ~ v1_relat_1(X2) ),
% 2.81/1.01      inference(renaming,[status(thm)],[c_183]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3340,plain,
% 2.81/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.81/1.01      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
% 2.81/1.01      | v1_relat_1(X1) != iProver_top
% 2.81/1.01      | v1_relat_1(X2) != iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3,plain,
% 2.81/1.01      ( ~ r1_tarski(X0,X1)
% 2.81/1.01      | ~ r1_tarski(X0,X2)
% 2.81/1.01      | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
% 2.81/1.01      inference(cnf_transformation,[],[f103]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3367,plain,
% 2.81/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.81/1.01      | r1_tarski(X0,X2) != iProver_top
% 2.81/1.01      | r1_tarski(X0,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_31,negated_conjecture,
% 2.81/1.01      ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
% 2.81/1.01      inference(cnf_transformation,[],[f113]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3344,plain,
% 2.81/1.01      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) != iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_6818,plain,
% 2.81/1.01      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) != iProver_top
% 2.81/1.01      | r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3367,c_3344]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7196,plain,
% 2.81/1.01      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
% 2.81/1.01      | v1_relat_1(sK4) != iProver_top
% 2.81/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3340,c_6818]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_34,negated_conjecture,
% 2.81/1.01      ( v1_relat_1(sK2) ),
% 2.81/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_35,plain,
% 2.81/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_32,negated_conjecture,
% 2.81/1.01      ( v1_relat_1(sK4) ),
% 2.81/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_37,plain,
% 2.81/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7978,plain,
% 2.81/1.01      ( r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
% 2.81/1.01      inference(global_propositional_subsumption,
% 2.81/1.01                [status(thm)],
% 2.81/1.01                [c_7196,c_35,c_37]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7984,plain,
% 2.81/1.01      ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top
% 2.81/1.01      | v1_relat_1(sK3) != iProver_top
% 2.81/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3340,c_7978]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_33,negated_conjecture,
% 2.81/1.01      ( v1_relat_1(sK3) ),
% 2.81/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_36,plain,
% 2.81/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7987,plain,
% 2.81/1.01      ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top
% 2.81/1.01      | r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top ),
% 2.81/1.01      inference(global_propositional_subsumption,
% 2.81/1.01                [status(thm)],
% 2.81/1.01                [c_7984,c_35,c_36]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_2,plain,
% 2.81/1.01      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
% 2.81/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3368,plain,
% 2.81/1.01      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_7993,plain,
% 2.81/1.01      ( r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
% 2.81/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_7987,c_3368]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_8252,plain,
% 2.81/1.01      ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_7315,c_7993]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_18,plain,
% 2.81/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X0,X5) ),
% 2.81/1.01      inference(cnf_transformation,[],[f114]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_3353,plain,
% 2.81/1.01      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 2.81/1.01      | r2_hidden(X0,X5) = iProver_top ),
% 2.81/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_4878,plain,
% 2.81/1.01      ( r2_hidden(X0,k4_enumset1(X1,X1,X2,X3,X4,X0)) = iProver_top ),
% 2.81/1.01      inference(superposition,[status(thm)],[c_3346,c_3353]) ).
% 2.81/1.01  
% 2.81/1.01  cnf(c_8291,plain,
% 2.81/1.01      ( $false ),
% 2.81/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_8252,c_4878]) ).
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/1.01  
% 2.81/1.01  ------                               Statistics
% 2.81/1.01  
% 2.81/1.01  ------ General
% 2.81/1.01  
% 2.81/1.01  abstr_ref_over_cycles:                  0
% 2.81/1.01  abstr_ref_under_cycles:                 0
% 2.81/1.01  gc_basic_clause_elim:                   0
% 2.81/1.01  forced_gc_time:                         0
% 2.81/1.01  parsing_time:                           0.009
% 2.81/1.01  unif_index_cands_time:                  0.
% 2.81/1.01  unif_index_add_time:                    0.
% 2.81/1.01  orderings_time:                         0.
% 2.81/1.01  out_proof_time:                         0.009
% 2.81/1.01  total_time:                             0.261
% 2.81/1.01  num_of_symbols:                         48
% 2.81/1.01  num_of_terms:                           9297
% 2.81/1.01  
% 2.81/1.01  ------ Preprocessing
% 2.81/1.01  
% 2.81/1.01  num_of_splits:                          0
% 2.81/1.01  num_of_split_atoms:                     0
% 2.81/1.01  num_of_reused_defs:                     0
% 2.81/1.01  num_eq_ax_congr_red:                    45
% 2.81/1.01  num_of_sem_filtered_clauses:            1
% 2.81/1.01  num_of_subtypes:                        0
% 2.81/1.01  monotx_restored_types:                  0
% 2.81/1.01  sat_num_of_epr_types:                   0
% 2.81/1.01  sat_num_of_non_cyclic_types:            0
% 2.81/1.01  sat_guarded_non_collapsed_types:        0
% 2.81/1.01  num_pure_diseq_elim:                    0
% 2.81/1.01  simp_replaced_by:                       0
% 2.81/1.01  res_preprocessed:                       154
% 2.81/1.01  prep_upred:                             0
% 2.81/1.01  prep_unflattend:                        90
% 2.81/1.01  smt_new_axioms:                         0
% 2.81/1.01  pred_elim_cands:                        5
% 2.81/1.01  pred_elim:                              2
% 2.81/1.01  pred_elim_cl:                           3
% 2.81/1.01  pred_elim_cycles:                       7
% 2.81/1.01  merged_defs:                            10
% 2.81/1.01  merged_defs_ncl:                        0
% 2.81/1.01  bin_hyper_res:                          11
% 2.81/1.01  prep_cycles:                            4
% 2.81/1.01  pred_elim_time:                         0.026
% 2.81/1.01  splitting_time:                         0.
% 2.81/1.01  sem_filter_time:                        0.
% 2.81/1.01  monotx_time:                            0.001
% 2.81/1.01  subtype_inf_time:                       0.
% 2.81/1.01  
% 2.81/1.01  ------ Problem properties
% 2.81/1.01  
% 2.81/1.01  clauses:                                32
% 2.81/1.01  conjectures:                            4
% 2.81/1.01  epr:                                    11
% 2.81/1.01  horn:                                   28
% 2.81/1.01  ground:                                 4
% 2.81/1.01  unary:                                  9
% 2.81/1.01  binary:                                 10
% 2.81/1.01  lits:                                   77
% 2.81/1.01  lits_eq:                                21
% 2.81/1.01  fd_pure:                                0
% 2.81/1.01  fd_pseudo:                              0
% 2.81/1.01  fd_cond:                                2
% 2.81/1.01  fd_pseudo_cond:                         2
% 2.81/1.01  ac_symbols:                             0
% 2.81/1.01  
% 2.81/1.01  ------ Propositional Solver
% 2.81/1.01  
% 2.81/1.01  prop_solver_calls:                      26
% 2.81/1.01  prop_fast_solver_calls:                 1279
% 2.81/1.01  smt_solver_calls:                       0
% 2.81/1.01  smt_fast_solver_calls:                  0
% 2.81/1.01  prop_num_of_clauses:                    2358
% 2.81/1.01  prop_preprocess_simplified:             8869
% 2.81/1.01  prop_fo_subsumed:                       8
% 2.81/1.01  prop_solver_time:                       0.
% 2.81/1.01  smt_solver_time:                        0.
% 2.81/1.01  smt_fast_solver_time:                   0.
% 2.81/1.01  prop_fast_solver_time:                  0.
% 2.81/1.01  prop_unsat_core_time:                   0.
% 2.81/1.01  
% 2.81/1.01  ------ QBF
% 2.81/1.01  
% 2.81/1.01  qbf_q_res:                              0
% 2.81/1.01  qbf_num_tautologies:                    0
% 2.81/1.01  qbf_prep_cycles:                        0
% 2.81/1.01  
% 2.81/1.01  ------ BMC1
% 2.81/1.01  
% 2.81/1.01  bmc1_current_bound:                     -1
% 2.81/1.01  bmc1_last_solved_bound:                 -1
% 2.81/1.01  bmc1_unsat_core_size:                   -1
% 2.81/1.01  bmc1_unsat_core_parents_size:           -1
% 2.81/1.01  bmc1_merge_next_fun:                    0
% 2.81/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.81/1.01  
% 2.81/1.01  ------ Instantiation
% 2.81/1.01  
% 2.81/1.01  inst_num_of_clauses:                    703
% 2.81/1.01  inst_num_in_passive:                    109
% 2.81/1.01  inst_num_in_active:                     252
% 2.81/1.01  inst_num_in_unprocessed:                342
% 2.81/1.01  inst_num_of_loops:                      260
% 2.81/1.01  inst_num_of_learning_restarts:          0
% 2.81/1.01  inst_num_moves_active_passive:          7
% 2.81/1.01  inst_lit_activity:                      0
% 2.81/1.01  inst_lit_activity_moves:                0
% 2.81/1.01  inst_num_tautologies:                   0
% 2.81/1.01  inst_num_prop_implied:                  0
% 2.81/1.01  inst_num_existing_simplified:           0
% 2.81/1.01  inst_num_eq_res_simplified:             0
% 2.81/1.01  inst_num_child_elim:                    0
% 2.81/1.01  inst_num_of_dismatching_blockings:      305
% 2.81/1.01  inst_num_of_non_proper_insts:           738
% 2.81/1.01  inst_num_of_duplicates:                 0
% 2.81/1.01  inst_inst_num_from_inst_to_res:         0
% 2.81/1.01  inst_dismatching_checking_time:         0.
% 2.81/1.01  
% 2.81/1.01  ------ Resolution
% 2.81/1.01  
% 2.81/1.01  res_num_of_clauses:                     0
% 2.81/1.01  res_num_in_passive:                     0
% 2.81/1.01  res_num_in_active:                      0
% 2.81/1.01  res_num_of_loops:                       158
% 2.81/1.01  res_forward_subset_subsumed:            32
% 2.81/1.01  res_backward_subset_subsumed:           2
% 2.81/1.01  res_forward_subsumed:                   0
% 2.81/1.01  res_backward_subsumed:                  0
% 2.81/1.01  res_forward_subsumption_resolution:     0
% 2.81/1.01  res_backward_subsumption_resolution:    0
% 2.81/1.01  res_clause_to_clause_subsumption:       1629
% 2.81/1.01  res_orphan_elimination:                 0
% 2.81/1.01  res_tautology_del:                      52
% 2.81/1.01  res_num_eq_res_simplified:              0
% 2.81/1.01  res_num_sel_changes:                    0
% 2.81/1.01  res_moves_from_active_to_pass:          0
% 2.81/1.01  
% 2.81/1.01  ------ Superposition
% 2.81/1.01  
% 2.81/1.01  sup_time_total:                         0.
% 2.81/1.01  sup_time_generating:                    0.
% 2.81/1.01  sup_time_sim_full:                      0.
% 2.81/1.01  sup_time_sim_immed:                     0.
% 2.81/1.01  
% 2.81/1.01  sup_num_of_clauses:                     76
% 2.81/1.01  sup_num_in_active:                      49
% 2.81/1.01  sup_num_in_passive:                     27
% 2.81/1.01  sup_num_of_loops:                       51
% 2.81/1.01  sup_fw_superposition:                   36
% 2.81/1.01  sup_bw_superposition:                   22
% 2.81/1.01  sup_immediate_simplified:               9
% 2.81/1.01  sup_given_eliminated:                   0
% 2.81/1.01  comparisons_done:                       0
% 2.81/1.01  comparisons_avoided:                    0
% 2.81/1.01  
% 2.81/1.01  ------ Simplifications
% 2.81/1.01  
% 2.81/1.01  
% 2.81/1.01  sim_fw_subset_subsumed:                 0
% 2.81/1.01  sim_bw_subset_subsumed:                 1
% 2.81/1.01  sim_fw_subsumed:                        3
% 2.81/1.01  sim_bw_subsumed:                        0
% 2.81/1.01  sim_fw_subsumption_res:                 3
% 2.81/1.01  sim_bw_subsumption_res:                 0
% 2.81/1.01  sim_tautology_del:                      5
% 2.81/1.01  sim_eq_tautology_del:                   5
% 2.81/1.01  sim_eq_res_simp:                        0
% 2.81/1.01  sim_fw_demodulated:                     2
% 2.81/1.01  sim_bw_demodulated:                     2
% 2.81/1.01  sim_light_normalised:                   5
% 2.81/1.01  sim_joinable_taut:                      0
% 2.81/1.01  sim_joinable_simp:                      0
% 2.81/1.01  sim_ac_normalised:                      0
% 2.81/1.01  sim_smt_subsumption:                    0
% 2.81/1.01  
%------------------------------------------------------------------------------
