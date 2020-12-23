%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:27 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 340 expanded)
%              Number of leaves         :   34 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  390 ( 737 expanded)
%              Number of equality atoms :  119 ( 275 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f145,f148,f152,f155,f160,f233,f236,f624,f631,f656])).

fof(f656,plain,(
    ~ spl5_38 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | ~ spl5_38 ),
    inference(trivial_inequality_removal,[],[f645])).

fof(f645,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_38 ),
    inference(superposition,[],[f400,f619])).

fof(f619,plain,
    ( k1_xboole_0 = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl5_38
  <=> k1_xboole_0 = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f400,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f89,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X3))) ),
    inference(definition_unfolding,[],[f68,f80,f84,f82,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f89,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f55,f84,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f631,plain,(
    spl5_39 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | spl5_39 ),
    inference(resolution,[],[f629,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f77,f81])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f629,plain,
    ( ! [X6,X7] : ~ sP0(sK3,X6,X7,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))
    | spl5_39 ),
    inference(resolution,[],[f623,f97])).

fof(f97,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f623,plain,
    ( ~ r2_hidden(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl5_39
  <=> r2_hidden(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f624,plain,
    ( spl5_38
    | ~ spl5_39
    | spl5_16 ),
    inference(avatar_split_clause,[],[f611,f230,f621,f617])).

fof(f230,plain,
    ( spl5_16
  <=> r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f611,plain,
    ( ~ r2_hidden(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))
    | k1_xboole_0 = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | spl5_16 ),
    inference(resolution,[],[f608,f232])).

fof(f232,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK3)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f230])).

fof(f608,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f607])).

fof(f607,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f110,f87])).

fof(f87,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f82])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X0)))
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = k4_enumset1(X2,X2,X2,X2,X2,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f236,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f228,f48])).

fof(f48,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,sK3)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK1,X1),k5_relat_1(sK1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK1,X1),k5_relat_1(sK1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,X2)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,X2)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,sK3)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f228,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f233,plain,
    ( ~ spl5_3
    | ~ spl5_15
    | ~ spl5_5
    | ~ spl5_16
    | spl5_2 ),
    inference(avatar_split_clause,[],[f224,f124,f230,f138,f226,f130])).

fof(f130,plain,
    ( spl5_3
  <=> v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f138,plain,
    ( spl5_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f124,plain,
    ( spl5_2
  <=> r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f224,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl5_2 ),
    inference(resolution,[],[f126,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f126,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f160,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f156,f47])).

fof(f47,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f156,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(resolution,[],[f153,f101])).

fof(f101,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_3 ),
    inference(resolution,[],[f132,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f155,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f144,f88])).

fof(f144,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_6
  <=> r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f152,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f140,f46])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f140,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f148,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f136,f47])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f145,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f128,f120,f142,f138,f134,f130])).

fof(f120,plain,
    ( spl5_1
  <=> r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f128,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl5_1 ),
    inference(resolution,[],[f122,f51])).

fof(f122,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f127,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f116,f124,f120])).

fof(f116,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK3))
    | ~ r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f90,f86])).

fof(f86,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k1_setfam_1(k4_enumset1(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)))) ),
    inference(definition_unfolding,[],[f49,f83,f83])).

fof(f49,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,sK3)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f83])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:32:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (19730)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (19732)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19757)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (19750)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (19732)Refutation not found, incomplete strategy% (19732)------------------------------
% 0.21/0.52  % (19732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19739)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (19732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19732)Memory used [KB]: 10746
% 0.21/0.53  % (19732)Time elapsed: 0.101 s
% 0.21/0.53  % (19732)------------------------------
% 0.21/0.53  % (19732)------------------------------
% 0.21/0.53  % (19737)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (19752)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (19750)Refutation not found, incomplete strategy% (19750)------------------------------
% 0.21/0.53  % (19750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19750)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19750)Memory used [KB]: 10746
% 0.21/0.53  % (19750)Time elapsed: 0.117 s
% 0.21/0.53  % (19750)------------------------------
% 0.21/0.53  % (19750)------------------------------
% 0.21/0.54  % (19758)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19744)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (19731)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (19754)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19733)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (19735)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (19734)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (19734)Refutation not found, incomplete strategy% (19734)------------------------------
% 0.21/0.55  % (19734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19734)Memory used [KB]: 6268
% 0.21/0.55  % (19734)Time elapsed: 0.125 s
% 0.21/0.55  % (19734)------------------------------
% 0.21/0.55  % (19734)------------------------------
% 0.21/0.55  % (19741)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (19742)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (19743)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (19753)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (19746)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (19736)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (19745)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (19755)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (19756)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (19740)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (19751)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (19740)Refutation not found, incomplete strategy% (19740)------------------------------
% 0.21/0.56  % (19740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19740)Memory used [KB]: 10618
% 0.21/0.56  % (19740)Time elapsed: 0.148 s
% 0.21/0.56  % (19740)------------------------------
% 0.21/0.56  % (19740)------------------------------
% 0.21/0.56  % (19751)Refutation not found, incomplete strategy% (19751)------------------------------
% 0.21/0.56  % (19751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19751)Memory used [KB]: 1791
% 0.21/0.56  % (19751)Time elapsed: 0.140 s
% 0.21/0.56  % (19751)------------------------------
% 0.21/0.56  % (19751)------------------------------
% 0.21/0.56  % (19738)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (19747)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (19748)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (19759)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (19738)Refutation not found, incomplete strategy% (19738)------------------------------
% 0.21/0.56  % (19738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19738)Memory used [KB]: 10746
% 0.21/0.56  % (19738)Time elapsed: 0.149 s
% 0.21/0.56  % (19738)------------------------------
% 0.21/0.56  % (19738)------------------------------
% 0.21/0.57  % (19747)Refutation not found, incomplete strategy% (19747)------------------------------
% 0.21/0.57  % (19747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19747)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (19747)Memory used [KB]: 10618
% 0.21/0.57  % (19747)Time elapsed: 0.150 s
% 0.21/0.57  % (19747)------------------------------
% 0.21/0.57  % (19747)------------------------------
% 1.50/0.57  % (19749)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.58  % (19755)Refutation not found, incomplete strategy% (19755)------------------------------
% 1.50/0.58  % (19755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (19755)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (19755)Memory used [KB]: 6652
% 1.50/0.58  % (19755)Time elapsed: 0.145 s
% 1.50/0.58  % (19755)------------------------------
% 1.50/0.58  % (19755)------------------------------
% 1.50/0.58  % (19742)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.58  % SZS output start Proof for theBenchmark
% 1.50/0.58  fof(f669,plain,(
% 1.50/0.58    $false),
% 1.50/0.58    inference(avatar_sat_refutation,[],[f127,f145,f148,f152,f155,f160,f233,f236,f624,f631,f656])).
% 1.50/0.58  fof(f656,plain,(
% 1.50/0.58    ~spl5_38),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f655])).
% 1.50/0.58  fof(f655,plain,(
% 1.50/0.58    $false | ~spl5_38),
% 1.50/0.58    inference(trivial_inequality_removal,[],[f645])).
% 1.50/0.58  fof(f645,plain,(
% 1.50/0.58    k1_xboole_0 != k1_xboole_0 | ~spl5_38),
% 1.50/0.58    inference(superposition,[],[f400,f619])).
% 1.50/0.58  fof(f619,plain,(
% 1.50/0.58    k1_xboole_0 = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) | ~spl5_38),
% 1.50/0.58    inference(avatar_component_clause,[],[f617])).
% 1.50/0.58  fof(f617,plain,(
% 1.50/0.58    spl5_38 <=> k1_xboole_0 = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.50/0.58  fof(f400,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.58    inference(superposition,[],[f89,f94])).
% 1.50/0.58  fof(f94,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X3)))) )),
% 1.50/0.58    inference(definition_unfolding,[],[f68,f80,f84,f82,f82])).
% 1.50/0.58  fof(f82,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f57,f81])).
% 1.50/0.58  fof(f81,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f62,f80])).
% 1.50/0.58  fof(f62,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f8])).
% 1.50/0.58  fof(f8,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.58  fof(f57,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f7])).
% 1.50/0.58  fof(f7,axiom,(
% 1.50/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.58  fof(f84,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.58    inference(definition_unfolding,[],[f58,f82])).
% 1.50/0.58  fof(f58,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f11])).
% 1.50/0.58  fof(f11,axiom,(
% 1.50/0.58    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.58  fof(f80,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f67,f79])).
% 1.50/0.58  fof(f79,plain,(
% 1.50/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f10])).
% 1.50/0.58  fof(f10,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.58  fof(f67,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f9])).
% 1.50/0.58  fof(f9,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.58  fof(f68,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f5])).
% 1.50/0.58  fof(f5,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.50/0.58  fof(f89,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),X1))) )),
% 1.50/0.58    inference(definition_unfolding,[],[f55,f84,f85])).
% 1.50/0.58  fof(f85,plain,(
% 1.50/0.58    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f50,f82])).
% 1.50/0.58  fof(f50,plain,(
% 1.50/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f6])).
% 1.50/0.58  fof(f6,axiom,(
% 1.50/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.58  fof(f55,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 1.50/0.58    inference(cnf_transformation,[],[f13])).
% 1.50/0.58  fof(f13,axiom,(
% 1.50/0.58    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.50/0.58  fof(f631,plain,(
% 1.50/0.58    spl5_39),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f630])).
% 1.50/0.58  fof(f630,plain,(
% 1.50/0.58    $false | spl5_39),
% 1.50/0.58    inference(resolution,[],[f629,f100])).
% 1.50/0.58  fof(f100,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k4_enumset1(X0,X0,X0,X0,X1,X2))) )),
% 1.50/0.58    inference(equality_resolution,[],[f96])).
% 1.50/0.58  fof(f96,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 1.50/0.58    inference(definition_unfolding,[],[f77,f81])).
% 1.50/0.58  fof(f77,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.50/0.58    inference(cnf_transformation,[],[f45])).
% 1.50/0.58  fof(f45,plain,(
% 1.50/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.50/0.58    inference(nnf_transformation,[],[f32])).
% 1.50/0.58  fof(f32,plain,(
% 1.50/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.50/0.58    inference(definition_folding,[],[f30,f31])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.50/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.74/0.60    inference(ennf_transformation,[],[f4])).
% 1.74/0.60  fof(f4,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.74/0.60  fof(f629,plain,(
% 1.74/0.60    ( ! [X6,X7] : (~sP0(sK3,X6,X7,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) ) | spl5_39),
% 1.74/0.60    inference(resolution,[],[f623,f97])).
% 1.74/0.60  fof(f97,plain,(
% 1.74/0.60    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X1,X2,X3)) )),
% 1.74/0.60    inference(equality_resolution,[],[f72])).
% 1.74/0.60  fof(f72,plain,(
% 1.74/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f44])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.74/0.60    inference(rectify,[],[f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.74/0.60    inference(flattening,[],[f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.74/0.60    inference(nnf_transformation,[],[f31])).
% 1.74/0.60  fof(f623,plain,(
% 1.74/0.60    ~r2_hidden(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) | spl5_39),
% 1.74/0.60    inference(avatar_component_clause,[],[f621])).
% 1.74/0.60  fof(f621,plain,(
% 1.74/0.60    spl5_39 <=> r2_hidden(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.74/0.60  fof(f624,plain,(
% 1.74/0.60    spl5_38 | ~spl5_39 | spl5_16),
% 1.74/0.60    inference(avatar_split_clause,[],[f611,f230,f621,f617])).
% 1.74/0.60  fof(f230,plain,(
% 1.74/0.60    spl5_16 <=> r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK3)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.74/0.60  fof(f611,plain,(
% 1.74/0.60    ~r2_hidden(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) | k1_xboole_0 = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) | spl5_16),
% 1.74/0.60    inference(resolution,[],[f608,f232])).
% 1.74/0.60  fof(f232,plain,(
% 1.74/0.60    ~r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK3) | spl5_16),
% 1.74/0.60    inference(avatar_component_clause,[],[f230])).
% 1.74/0.60  fof(f608,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f607])).
% 1.74/0.60  fof(f607,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 1.74/0.60    inference(superposition,[],[f110,f87])).
% 1.74/0.60  fof(f87,plain,(
% 1.74/0.60    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.74/0.60    inference(definition_unfolding,[],[f53,f83])).
% 1.74/0.60  fof(f83,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f56,f82])).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f14])).
% 1.74/0.60  fof(f14,axiom,(
% 1.74/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.74/0.60  fof(f53,plain,(
% 1.74/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,plain,(
% 1.74/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.74/0.60    inference(rectify,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.74/0.60  fof(f110,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X0))) | ~r2_hidden(X2,X1) | k1_xboole_0 = k4_enumset1(X2,X2,X2,X2,X2,X0) | ~r2_hidden(X0,X1)) )),
% 1.74/0.60    inference(resolution,[],[f91,f59])).
% 1.74/0.60  fof(f59,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f27])).
% 1.74/0.60  fof(f27,plain,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.74/0.60    inference(flattening,[],[f26])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f16])).
% 1.74/0.60  fof(f16,axiom,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.74/0.60  fof(f91,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f66,f82])).
% 1.74/0.60  fof(f66,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f39])).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.74/0.60    inference(flattening,[],[f38])).
% 1.74/0.60  fof(f38,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.74/0.60    inference(nnf_transformation,[],[f12])).
% 1.74/0.60  fof(f12,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.74/0.60  fof(f236,plain,(
% 1.74/0.60    spl5_15),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f234])).
% 1.74/0.60  fof(f234,plain,(
% 1.74/0.60    $false | spl5_15),
% 1.74/0.60    inference(resolution,[],[f228,f48])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    v1_relat_1(sK3)),
% 1.74/0.60    inference(cnf_transformation,[],[f36])).
% 1.74/0.60  fof(f36,plain,(
% 1.74/0.60    ((~r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,sK3)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f35,f34,f33])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK1,X1),k5_relat_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f34,plain,(
% 1.74/0.60    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK1,X1),k5_relat_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,X2)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(sK2))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f35,plain,(
% 1.74/0.60    ? [X2] : (~r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,X2)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,sK3)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))) & v1_relat_1(sK3))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f22,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f20])).
% 1.74/0.60  fof(f20,negated_conjecture,(
% 1.74/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.74/0.60    inference(negated_conjecture,[],[f19])).
% 1.74/0.60  fof(f19,conjecture,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.74/0.60  fof(f228,plain,(
% 1.74/0.60    ~v1_relat_1(sK3) | spl5_15),
% 1.74/0.60    inference(avatar_component_clause,[],[f226])).
% 1.74/0.60  fof(f226,plain,(
% 1.74/0.60    spl5_15 <=> v1_relat_1(sK3)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.74/0.60  fof(f233,plain,(
% 1.74/0.60    ~spl5_3 | ~spl5_15 | ~spl5_5 | ~spl5_16 | spl5_2),
% 1.74/0.60    inference(avatar_split_clause,[],[f224,f124,f230,f138,f226,f130])).
% 1.74/0.60  fof(f130,plain,(
% 1.74/0.60    spl5_3 <=> v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.74/0.60  fof(f138,plain,(
% 1.74/0.60    spl5_5 <=> v1_relat_1(sK1)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.74/0.60  fof(f124,plain,(
% 1.74/0.60    spl5_2 <=> r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK3))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.74/0.60  fof(f224,plain,(
% 1.74/0.60    ~r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(sK1) | ~v1_relat_1(sK3) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) | spl5_2),
% 1.74/0.60    inference(resolution,[],[f126,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f24])).
% 1.74/0.60  fof(f24,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f23])).
% 1.74/0.60  fof(f23,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f18])).
% 1.74/0.60  fof(f18,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 1.74/0.60  fof(f126,plain,(
% 1.74/0.60    ~r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK3)) | spl5_2),
% 1.74/0.60    inference(avatar_component_clause,[],[f124])).
% 1.74/0.60  fof(f160,plain,(
% 1.74/0.60    spl5_3),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f158])).
% 1.74/0.60  fof(f158,plain,(
% 1.74/0.60    $false | spl5_3),
% 1.74/0.60    inference(resolution,[],[f156,f47])).
% 1.74/0.60  fof(f47,plain,(
% 1.74/0.60    v1_relat_1(sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f36])).
% 1.74/0.60  fof(f156,plain,(
% 1.74/0.60    ~v1_relat_1(sK2) | spl5_3),
% 1.74/0.60    inference(resolution,[],[f153,f101])).
% 1.74/0.60  fof(f101,plain,(
% 1.74/0.60    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 1.74/0.60    inference(resolution,[],[f88,f61])).
% 1.74/0.60  fof(f61,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f37])).
% 1.74/0.60  fof(f37,plain,(
% 1.74/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.74/0.60    inference(nnf_transformation,[],[f15])).
% 1.74/0.60  fof(f15,axiom,(
% 1.74/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.74/0.60  fof(f88,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f54,f83])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f2,axiom,(
% 1.74/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.74/0.60  fof(f153,plain,(
% 1.74/0.60    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_3),
% 1.74/0.60    inference(resolution,[],[f132,f52])).
% 1.74/0.60  fof(f52,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f25])).
% 1.74/0.60  fof(f25,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f17])).
% 1.74/0.60  fof(f17,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.74/0.60  fof(f132,plain,(
% 1.74/0.60    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) | spl5_3),
% 1.74/0.60    inference(avatar_component_clause,[],[f130])).
% 1.74/0.60  fof(f155,plain,(
% 1.74/0.60    spl5_6),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f154])).
% 1.74/0.60  fof(f154,plain,(
% 1.74/0.60    $false | spl5_6),
% 1.74/0.60    inference(resolution,[],[f144,f88])).
% 1.74/0.60  fof(f144,plain,(
% 1.74/0.60    ~r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK2) | spl5_6),
% 1.74/0.60    inference(avatar_component_clause,[],[f142])).
% 1.74/0.60  fof(f142,plain,(
% 1.74/0.60    spl5_6 <=> r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK2)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.74/0.60  fof(f152,plain,(
% 1.74/0.60    spl5_5),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f150])).
% 1.74/0.60  fof(f150,plain,(
% 1.74/0.60    $false | spl5_5),
% 1.74/0.60    inference(resolution,[],[f140,f46])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    v1_relat_1(sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f36])).
% 1.74/0.60  fof(f140,plain,(
% 1.74/0.60    ~v1_relat_1(sK1) | spl5_5),
% 1.74/0.60    inference(avatar_component_clause,[],[f138])).
% 1.74/0.60  fof(f148,plain,(
% 1.74/0.60    spl5_4),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f146])).
% 1.74/0.60  fof(f146,plain,(
% 1.74/0.60    $false | spl5_4),
% 1.74/0.60    inference(resolution,[],[f136,f47])).
% 1.74/0.60  fof(f136,plain,(
% 1.74/0.60    ~v1_relat_1(sK2) | spl5_4),
% 1.74/0.60    inference(avatar_component_clause,[],[f134])).
% 1.74/0.60  fof(f134,plain,(
% 1.74/0.60    spl5_4 <=> v1_relat_1(sK2)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.74/0.60  fof(f145,plain,(
% 1.74/0.60    ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_1),
% 1.74/0.60    inference(avatar_split_clause,[],[f128,f120,f142,f138,f134,f130])).
% 1.74/0.60  fof(f120,plain,(
% 1.74/0.60    spl5_1 <=> r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK2))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.74/0.60  fof(f128,plain,(
% 1.74/0.60    ~r1_tarski(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) | spl5_1),
% 1.74/0.60    inference(resolution,[],[f122,f51])).
% 1.74/0.60  fof(f122,plain,(
% 1.74/0.60    ~r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK2)) | spl5_1),
% 1.74/0.60    inference(avatar_component_clause,[],[f120])).
% 1.74/0.60  fof(f127,plain,(
% 1.74/0.60    ~spl5_1 | ~spl5_2),
% 1.74/0.60    inference(avatar_split_clause,[],[f116,f124,f120])).
% 1.74/0.60  fof(f116,plain,(
% 1.74/0.60    ~r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK3)) | ~r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k5_relat_1(sK1,sK2))),
% 1.74/0.60    inference(resolution,[],[f90,f86])).
% 1.74/0.60  fof(f86,plain,(
% 1.74/0.60    ~r1_tarski(k5_relat_1(sK1,k1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),k1_setfam_1(k4_enumset1(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))))),
% 1.74/0.60    inference(definition_unfolding,[],[f49,f83,f83])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    ~r1_tarski(k5_relat_1(sK1,k3_xboole_0(sK2,sK3)),k3_xboole_0(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)))),
% 1.74/0.60    inference(cnf_transformation,[],[f36])).
% 1.74/0.60  fof(f90,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f63,f83])).
% 1.74/0.60  fof(f63,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f29])).
% 1.74/0.60  fof(f29,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.74/0.60    inference(flattening,[],[f28])).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.74/0.60    inference(ennf_transformation,[],[f3])).
% 1.74/0.60  fof(f3,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (19742)------------------------------
% 1.74/0.60  % (19742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (19742)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (19742)Memory used [KB]: 6524
% 1.74/0.60  % (19742)Time elapsed: 0.148 s
% 1.74/0.60  % (19742)------------------------------
% 1.74/0.60  % (19742)------------------------------
% 1.74/0.60  % (19729)Success in time 0.235 s
%------------------------------------------------------------------------------
