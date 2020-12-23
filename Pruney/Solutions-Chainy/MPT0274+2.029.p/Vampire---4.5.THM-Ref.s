%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:24 EST 2020

% Result     : Theorem 4.20s
% Output     : Refutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 534 expanded)
%              Number of leaves         :   31 ( 183 expanded)
%              Depth                    :   13
%              Number of atoms          :  409 (1123 expanded)
%              Number of equality atoms :  104 ( 507 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f113,f114,f3149,f3156,f4051,f5235,f5236,f5256,f5271,f5372])).

fof(f5372,plain,
    ( spl8_3
    | ~ spl8_9
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f5371])).

fof(f5371,plain,
    ( $false
    | spl8_3
    | ~ spl8_9
    | spl8_12 ),
    inference(subsumption_resolution,[],[f5370,f3137])).

fof(f3137,plain,
    ( r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f3136])).

fof(f3136,plain,
    ( spl8_9
  <=> r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f5370,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_3
    | spl8_12 ),
    inference(subsumption_resolution,[],[f5367,f110])).

fof(f110,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_3
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f5367,plain,
    ( r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_12 ),
    inference(resolution,[],[f5358,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f5358,plain,
    ( ~ sP0(sK5,sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_12 ),
    inference(resolution,[],[f4035,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X1,X0))
      | ~ sP0(X1,X2,X0) ) ),
    inference(superposition,[],[f69,f54])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f25,f27])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f4035,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f4033])).

fof(f4033,plain,
    ( spl8_12
  <=> r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f5271,plain,
    ( ~ spl8_10
    | spl8_1 ),
    inference(avatar_split_clause,[],[f5270,f101,f3140])).

fof(f3140,plain,
    ( spl8_10
  <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f101,plain,
    ( spl8_1
  <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f5270,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f5264,f54])).

fof(f5264,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_1 ),
    inference(superposition,[],[f166,f220])).

fof(f220,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f202,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f202,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f62,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f166,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f103,f55])).

fof(f103,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f5256,plain,
    ( ~ spl8_11
    | ~ spl8_12
    | spl8_10 ),
    inference(avatar_split_clause,[],[f4027,f3140,f4033,f4029])).

fof(f4029,plain,
    ( spl8_11
  <=> r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f4027,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | ~ r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_10 ),
    inference(trivial_inequality_removal,[],[f4026])).

fof(f4026,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | ~ r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_10 ),
    inference(superposition,[],[f3142,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f88,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f81,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f82,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f3142,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f3140])).

fof(f5236,plain,
    ( ~ spl8_3
    | ~ spl8_1
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f5228,f3136,f101,f109])).

fof(f5228,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ spl8_1
    | ~ spl8_9 ),
    inference(resolution,[],[f4339,f3137])).

fof(f4339,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
        | ~ r2_hidden(X0,sK5) )
    | ~ spl8_1 ),
    inference(resolution,[],[f4227,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] : sP2(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f79,f87])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP2(X0,X1,X2,X3) )
      & ( sP2(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP2(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f26,f30,f29])).

fof(f29,plain,(
    ! [X4,X2,X1,X0] :
      ( sP1(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( sP2(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP1(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f4227,plain,
    ( ! [X23,X22] :
        ( ~ sP2(sK3,sK3,sK4,X22)
        | ~ r2_hidden(X23,sK5)
        | ~ r2_hidden(X23,X22) )
    | ~ spl8_1 ),
    inference(superposition,[],[f280,f4110])).

fof(f4110,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,k5_xboole_0(X0,sK5)) = X0
        | ~ sP2(sK3,sK3,sK4,X0) )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f4066,f220])).

fof(f4066,plain,
    ( ! [X0] :
        ( k5_xboole_0(X0,k3_xboole_0(sK5,X0)) = X0
        | ~ sP2(sK3,sK3,sK4,X0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f4052,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f80,f87])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4052,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f102,f55])).

fof(f102,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f280,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X5,k5_xboole_0(X5,X4)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(backward_demodulation,[],[f122,f220])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X5,k3_xboole_0(X4,X5)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f60,f116])).

fof(f116,plain,(
    ! [X2,X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f92,f55])).

fof(f92,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f5235,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f5227,f3132,f101,f105])).

fof(f105,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f3132,plain,
    ( spl8_8
  <=> r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f5227,plain,
    ( ~ r2_hidden(sK3,sK5)
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(resolution,[],[f4339,f3133])).

fof(f3133,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f3132])).

fof(f4051,plain,
    ( spl8_2
    | ~ spl8_8
    | spl8_11 ),
    inference(avatar_split_clause,[],[f4050,f4029,f3132,f105])).

fof(f4050,plain,
    ( r2_hidden(sK3,sK5)
    | ~ spl8_8
    | spl8_11 ),
    inference(subsumption_resolution,[],[f4044,f3133])).

fof(f4044,plain,
    ( r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_11 ),
    inference(resolution,[],[f4038,f66])).

fof(f4038,plain,
    ( ~ sP0(sK5,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_11 ),
    inference(resolution,[],[f4031,f132])).

fof(f4031,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f4029])).

fof(f3156,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f3155])).

fof(f3155,plain,
    ( $false
    | spl8_9 ),
    inference(subsumption_resolution,[],[f3153,f96])).

fof(f96,plain,(
    ! [X2,X3,X1] : sP1(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP1(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP1(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP1(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP1(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f3153,plain,
    ( ~ sP1(sK4,sK4,sK3,sK3)
    | spl8_9 ),
    inference(resolution,[],[f3138,f304])).

fof(f304,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f99,f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ sP1(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ( ~ sP1(sK7(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sP1(sK7(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP1(X5,X2,X1,X0) )
            & ( sP1(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP1(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP1(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP1(sK7(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sP1(sK7(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP1(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP1(X5,X2,X1,X0) )
            & ( sP1(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP1(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP1(X4,X2,X1,X0) )
            & ( sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f3138,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f3136])).

fof(f3149,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f3148])).

fof(f3148,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f3146,f97])).

fof(f97,plain,(
    ! [X2,X3,X1] : sP1(X2,X1,X2,X3) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3146,plain,
    ( ~ sP1(sK3,sK4,sK3,sK3)
    | spl8_8 ),
    inference(resolution,[],[f3134,f304])).

fof(f3134,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f3132])).

fof(f114,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f91,f105,f101])).

fof(f91,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f49,f88,f57,f88])).

fof(f49,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( r2_hidden(sK4,sK5)
      | r2_hidden(sK3,sK5)
      | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5) )
    & ( ( ~ r2_hidden(sK4,sK5)
        & ~ r2_hidden(sK3,sK5) )
      | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK4,sK5)
        | r2_hidden(sK3,sK5)
        | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5) )
      & ( ( ~ r2_hidden(sK4,sK5)
          & ~ r2_hidden(sK3,sK5) )
        | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f113,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f90,f109,f101])).

fof(f90,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f50,f88,f57,f88])).

fof(f50,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f89,f109,f105,f101])).

fof(f89,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f51,f88,f57,f88])).

fof(f51,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (7470)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (7466)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7478)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (7464)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (7462)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (7489)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (7487)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (7481)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (7461)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (7490)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (7465)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (7471)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (7478)Refutation not found, incomplete strategy% (7478)------------------------------
% 0.22/0.54  % (7478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7478)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7471)Refutation not found, incomplete strategy% (7471)------------------------------
% 0.22/0.54  % (7471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7471)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7471)Memory used [KB]: 10618
% 0.22/0.54  % (7471)Time elapsed: 0.125 s
% 0.22/0.54  % (7471)------------------------------
% 0.22/0.54  % (7471)------------------------------
% 0.22/0.54  % (7472)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (7463)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (7483)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (7469)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (7480)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (7473)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (7474)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (7469)Refutation not found, incomplete strategy% (7469)------------------------------
% 0.22/0.54  % (7469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7468)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (7463)Refutation not found, incomplete strategy% (7463)------------------------------
% 0.22/0.55  % (7463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7463)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7463)Memory used [KB]: 10746
% 0.22/0.55  % (7463)Time elapsed: 0.135 s
% 0.22/0.55  % (7463)------------------------------
% 0.22/0.55  % (7463)------------------------------
% 0.22/0.55  % (7488)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (7484)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.55  % (7478)Memory used [KB]: 10746
% 1.45/0.55  % (7478)Time elapsed: 0.119 s
% 1.45/0.55  % (7478)------------------------------
% 1.45/0.55  % (7478)------------------------------
% 1.45/0.55  % (7467)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.55  % (7482)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (7486)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (7472)Refutation not found, incomplete strategy% (7472)------------------------------
% 1.45/0.56  % (7472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (7472)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (7472)Memory used [KB]: 10618
% 1.45/0.56  % (7472)Time elapsed: 0.149 s
% 1.45/0.56  % (7472)------------------------------
% 1.45/0.56  % (7472)------------------------------
% 1.45/0.56  % (7475)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.56  % (7477)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (7485)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (7479)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.61/0.57  % (7469)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (7469)Memory used [KB]: 10618
% 1.61/0.57  % (7469)Time elapsed: 0.128 s
% 1.61/0.57  % (7469)------------------------------
% 1.61/0.57  % (7469)------------------------------
% 1.61/0.57  % (7476)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.21/0.66  % (7498)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.21/0.68  % (7496)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.69  % (7497)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.21/0.69  % (7499)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.21/0.71  % (7501)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.95/0.84  % (7466)Time limit reached!
% 2.95/0.84  % (7466)------------------------------
% 2.95/0.84  % (7466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.84  % (7466)Termination reason: Time limit
% 2.95/0.84  % (7466)Termination phase: Saturation
% 2.95/0.84  
% 2.95/0.84  % (7466)Memory used [KB]: 8571
% 2.95/0.84  % (7466)Time elapsed: 0.400 s
% 2.95/0.84  % (7466)------------------------------
% 2.95/0.84  % (7466)------------------------------
% 3.59/0.92  % (7473)Time limit reached!
% 3.59/0.92  % (7473)------------------------------
% 3.59/0.92  % (7473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.92  % (7473)Termination reason: Time limit
% 3.59/0.92  
% 3.59/0.92  % (7473)Memory used [KB]: 8699
% 3.59/0.92  % (7473)Time elapsed: 0.514 s
% 3.59/0.92  % (7473)------------------------------
% 3.59/0.92  % (7473)------------------------------
% 3.59/0.92  % (7461)Time limit reached!
% 3.59/0.92  % (7461)------------------------------
% 3.59/0.92  % (7461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.92  % (7461)Termination reason: Time limit
% 3.59/0.92  
% 3.59/0.92  % (7461)Memory used [KB]: 2430
% 3.59/0.92  % (7461)Time elapsed: 0.505 s
% 3.59/0.92  % (7461)------------------------------
% 3.59/0.92  % (7461)------------------------------
% 4.00/0.93  % (7552)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.00/0.94  % (7462)Time limit reached!
% 4.00/0.94  % (7462)------------------------------
% 4.00/0.94  % (7462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.94  % (7462)Termination reason: Time limit
% 4.00/0.94  % (7462)Termination phase: Saturation
% 4.00/0.94  
% 4.00/0.94  % (7462)Memory used [KB]: 9978
% 4.00/0.94  % (7462)Time elapsed: 0.500 s
% 4.00/0.94  % (7462)------------------------------
% 4.00/0.94  % (7462)------------------------------
% 4.20/0.98  % (7488)Refutation found. Thanks to Tanya!
% 4.20/0.98  % SZS status Theorem for theBenchmark
% 4.20/1.00  % SZS output start Proof for theBenchmark
% 4.20/1.00  fof(f5373,plain,(
% 4.20/1.00    $false),
% 4.20/1.00    inference(avatar_sat_refutation,[],[f112,f113,f114,f3149,f3156,f4051,f5235,f5236,f5256,f5271,f5372])).
% 4.20/1.00  fof(f5372,plain,(
% 4.20/1.00    spl8_3 | ~spl8_9 | spl8_12),
% 4.20/1.00    inference(avatar_contradiction_clause,[],[f5371])).
% 4.20/1.00  fof(f5371,plain,(
% 4.20/1.00    $false | (spl8_3 | ~spl8_9 | spl8_12)),
% 4.20/1.00    inference(subsumption_resolution,[],[f5370,f3137])).
% 4.20/1.00  fof(f3137,plain,(
% 4.20/1.00    r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~spl8_9),
% 4.20/1.00    inference(avatar_component_clause,[],[f3136])).
% 4.20/1.00  fof(f3136,plain,(
% 4.20/1.00    spl8_9 <=> r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 4.20/1.00  fof(f5370,plain,(
% 4.20/1.00    ~r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | (spl8_3 | spl8_12)),
% 4.20/1.00    inference(subsumption_resolution,[],[f5367,f110])).
% 4.20/1.00  fof(f110,plain,(
% 4.20/1.00    ~r2_hidden(sK4,sK5) | spl8_3),
% 4.20/1.00    inference(avatar_component_clause,[],[f109])).
% 4.20/1.00  fof(f109,plain,(
% 4.20/1.00    spl8_3 <=> r2_hidden(sK4,sK5)),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 4.20/1.00  fof(f5367,plain,(
% 4.20/1.00    r2_hidden(sK4,sK5) | ~r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_12),
% 4.20/1.00    inference(resolution,[],[f5358,f66])).
% 4.20/1.00  fof(f66,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f39])).
% 4.20/1.00  fof(f39,plain,(
% 4.20/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 4.20/1.00    inference(rectify,[],[f38])).
% 4.20/1.00  fof(f38,plain,(
% 4.20/1.00    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 4.20/1.00    inference(nnf_transformation,[],[f27])).
% 4.20/1.00  fof(f27,plain,(
% 4.20/1.00    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.20/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.20/1.00  fof(f5358,plain,(
% 4.20/1.00    ~sP0(sK5,sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_12),
% 4.20/1.00    inference(resolution,[],[f4035,f132])).
% 4.20/1.00  fof(f132,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X1,X0)) | ~sP0(X1,X2,X0)) )),
% 4.20/1.00    inference(superposition,[],[f69,f54])).
% 4.20/1.00  fof(f54,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f2])).
% 4.20/1.00  fof(f2,axiom,(
% 4.20/1.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.20/1.00  fof(f69,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f40])).
% 4.20/1.00  fof(f40,plain,(
% 4.20/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 4.20/1.00    inference(nnf_transformation,[],[f28])).
% 4.20/1.00  fof(f28,plain,(
% 4.20/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 4.20/1.00    inference(definition_folding,[],[f25,f27])).
% 4.20/1.00  fof(f25,plain,(
% 4.20/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.20/1.00    inference(ennf_transformation,[],[f4])).
% 4.20/1.00  fof(f4,axiom,(
% 4.20/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 4.20/1.00  fof(f4035,plain,(
% 4.20/1.00    ~r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_12),
% 4.20/1.00    inference(avatar_component_clause,[],[f4033])).
% 4.20/1.00  fof(f4033,plain,(
% 4.20/1.00    spl8_12 <=> r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 4.20/1.00  fof(f5271,plain,(
% 4.20/1.00    ~spl8_10 | spl8_1),
% 4.20/1.00    inference(avatar_split_clause,[],[f5270,f101,f3140])).
% 4.20/1.00  fof(f3140,plain,(
% 4.20/1.00    spl8_10 <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 4.20/1.00  fof(f101,plain,(
% 4.20/1.00    spl8_1 <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 4.20/1.00  fof(f5270,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_1),
% 4.20/1.00    inference(forward_demodulation,[],[f5264,f54])).
% 4.20/1.00  fof(f5264,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_1),
% 4.20/1.00    inference(superposition,[],[f166,f220])).
% 4.20/1.00  fof(f220,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.20/1.00    inference(forward_demodulation,[],[f202,f55])).
% 4.20/1.00  fof(f55,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f1])).
% 4.20/1.00  fof(f1,axiom,(
% 4.20/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.20/1.00  fof(f202,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 4.20/1.00    inference(superposition,[],[f62,f52])).
% 4.20/1.00  fof(f52,plain,(
% 4.20/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.20/1.00    inference(cnf_transformation,[],[f19])).
% 4.20/1.00  fof(f19,plain,(
% 4.20/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.20/1.00    inference(rectify,[],[f3])).
% 4.20/1.00  fof(f3,axiom,(
% 4.20/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.20/1.00  fof(f62,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f7])).
% 4.20/1.00  fof(f7,axiom,(
% 4.20/1.00    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 4.20/1.00  fof(f166,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_1),
% 4.20/1.00    inference(forward_demodulation,[],[f103,f55])).
% 4.20/1.00  fof(f103,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_1),
% 4.20/1.00    inference(avatar_component_clause,[],[f101])).
% 4.20/1.00  fof(f5256,plain,(
% 4.20/1.00    ~spl8_11 | ~spl8_12 | spl8_10),
% 4.20/1.00    inference(avatar_split_clause,[],[f4027,f3140,f4033,f4029])).
% 4.20/1.00  fof(f4029,plain,(
% 4.20/1.00    spl8_11 <=> r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 4.20/1.00  fof(f4027,plain,(
% 4.20/1.00    ~r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | ~r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_10),
% 4.20/1.00    inference(trivial_inequality_removal,[],[f4026])).
% 4.20/1.00  fof(f4026,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | ~r2_hidden(sK4,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | ~r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_10),
% 4.20/1.00    inference(superposition,[],[f3142,f93])).
% 4.20/1.00  fof(f93,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f63,f88,f88])).
% 4.20/1.00  fof(f88,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f56,f87])).
% 4.20/1.00  fof(f87,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f61,f86])).
% 4.20/1.00  fof(f86,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f70,f85])).
% 4.20/1.00  fof(f85,plain,(
% 4.20/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f81,f84])).
% 4.20/1.00  fof(f84,plain,(
% 4.20/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f82,f83])).
% 4.20/1.00  fof(f83,plain,(
% 4.20/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f15])).
% 4.20/1.00  fof(f15,axiom,(
% 4.20/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 4.20/1.00  fof(f82,plain,(
% 4.20/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f14])).
% 4.20/1.00  fof(f14,axiom,(
% 4.20/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 4.20/1.00  fof(f81,plain,(
% 4.20/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f13])).
% 4.20/1.00  fof(f13,axiom,(
% 4.20/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.20/1.00  fof(f70,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f12])).
% 4.20/1.00  fof(f12,axiom,(
% 4.20/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.20/1.00  fof(f61,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f11])).
% 4.20/1.00  fof(f11,axiom,(
% 4.20/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.20/1.00  fof(f56,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f10])).
% 4.20/1.00  fof(f10,axiom,(
% 4.20/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.20/1.00  fof(f63,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f24])).
% 4.20/1.00  fof(f24,plain,(
% 4.20/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 4.20/1.00    inference(flattening,[],[f23])).
% 4.20/1.00  fof(f23,plain,(
% 4.20/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 4.20/1.00    inference(ennf_transformation,[],[f16])).
% 4.20/1.00  fof(f16,axiom,(
% 4.20/1.00    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 4.20/1.00  fof(f3142,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_10),
% 4.20/1.00    inference(avatar_component_clause,[],[f3140])).
% 4.20/1.00  fof(f5236,plain,(
% 4.20/1.00    ~spl8_3 | ~spl8_1 | ~spl8_9),
% 4.20/1.00    inference(avatar_split_clause,[],[f5228,f3136,f101,f109])).
% 4.20/1.00  fof(f5228,plain,(
% 4.20/1.00    ~r2_hidden(sK4,sK5) | (~spl8_1 | ~spl8_9)),
% 4.20/1.00    inference(resolution,[],[f4339,f3137])).
% 4.20/1.00  fof(f4339,plain,(
% 4.20/1.00    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~r2_hidden(X0,sK5)) ) | ~spl8_1),
% 4.20/1.00    inference(resolution,[],[f4227,f99])).
% 4.20/1.00  fof(f99,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (sP2(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 4.20/1.00    inference(equality_resolution,[],[f95])).
% 4.20/1.00  fof(f95,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 4.20/1.00    inference(definition_unfolding,[],[f79,f87])).
% 4.20/1.00  fof(f79,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.20/1.00    inference(cnf_transformation,[],[f48])).
% 4.20/1.00  fof(f48,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP2(X0,X1,X2,X3)) & (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 4.20/1.00    inference(nnf_transformation,[],[f31])).
% 4.20/1.00  fof(f31,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP2(X0,X1,X2,X3))),
% 4.20/1.00    inference(definition_folding,[],[f26,f30,f29])).
% 4.20/1.00  fof(f29,plain,(
% 4.20/1.00    ! [X4,X2,X1,X0] : (sP1(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 4.20/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.20/1.00  fof(f30,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : (sP2(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP1(X4,X2,X1,X0)))),
% 4.20/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 4.20/1.00  fof(f26,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.20/1.00    inference(ennf_transformation,[],[f9])).
% 4.20/1.00  fof(f9,axiom,(
% 4.20/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 4.20/1.00  fof(f4227,plain,(
% 4.20/1.00    ( ! [X23,X22] : (~sP2(sK3,sK3,sK4,X22) | ~r2_hidden(X23,sK5) | ~r2_hidden(X23,X22)) ) | ~spl8_1),
% 4.20/1.00    inference(superposition,[],[f280,f4110])).
% 4.20/1.00  fof(f4110,plain,(
% 4.20/1.00    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,sK5)) = X0 | ~sP2(sK3,sK3,sK4,X0)) ) | ~spl8_1),
% 4.20/1.00    inference(forward_demodulation,[],[f4066,f220])).
% 4.20/1.00  fof(f4066,plain,(
% 4.20/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(sK5,X0)) = X0 | ~sP2(sK3,sK3,sK4,X0)) ) | ~spl8_1),
% 4.20/1.00    inference(superposition,[],[f4052,f94])).
% 4.20/1.00  fof(f94,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP2(X0,X1,X2,X3)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f80,f87])).
% 4.20/1.00  fof(f80,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP2(X0,X1,X2,X3)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f48])).
% 4.20/1.00  fof(f4052,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | ~spl8_1),
% 4.20/1.00    inference(forward_demodulation,[],[f102,f55])).
% 4.20/1.00  fof(f102,plain,(
% 4.20/1.00    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | ~spl8_1),
% 4.20/1.00    inference(avatar_component_clause,[],[f101])).
% 4.20/1.00  fof(f280,plain,(
% 4.20/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X5,k5_xboole_0(X5,X4))) | ~r2_hidden(X3,X4)) )),
% 4.20/1.00    inference(backward_demodulation,[],[f122,f220])).
% 4.20/1.00  fof(f122,plain,(
% 4.20/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(X5,k3_xboole_0(X4,X5))) | ~r2_hidden(X3,X4)) )),
% 4.20/1.00    inference(resolution,[],[f60,f116])).
% 4.20/1.00  fof(f116,plain,(
% 4.20/1.00    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) )),
% 4.20/1.00    inference(superposition,[],[f92,f55])).
% 4.20/1.00  fof(f92,plain,(
% 4.20/1.00    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.20/1.00    inference(definition_unfolding,[],[f53,f57])).
% 4.20/1.00  fof(f57,plain,(
% 4.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.20/1.00    inference(cnf_transformation,[],[f6])).
% 4.20/1.00  fof(f6,axiom,(
% 4.20/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.20/1.00  fof(f53,plain,(
% 4.20/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f8])).
% 4.20/1.00  fof(f8,axiom,(
% 4.20/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.20/1.00  fof(f60,plain,(
% 4.20/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f37])).
% 4.20/1.00  fof(f37,plain,(
% 4.20/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f36])).
% 4.20/1.00  fof(f36,plain,(
% 4.20/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 4.20/1.00    introduced(choice_axiom,[])).
% 4.20/1.00  fof(f22,plain,(
% 4.20/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.20/1.00    inference(ennf_transformation,[],[f20])).
% 4.20/1.00  fof(f20,plain,(
% 4.20/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.20/1.00    inference(rectify,[],[f5])).
% 4.20/1.00  fof(f5,axiom,(
% 4.20/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.20/1.00  fof(f5235,plain,(
% 4.20/1.00    ~spl8_2 | ~spl8_1 | ~spl8_8),
% 4.20/1.00    inference(avatar_split_clause,[],[f5227,f3132,f101,f105])).
% 4.20/1.00  fof(f105,plain,(
% 4.20/1.00    spl8_2 <=> r2_hidden(sK3,sK5)),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 4.20/1.00  fof(f3132,plain,(
% 4.20/1.00    spl8_8 <=> r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 4.20/1.00    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 4.20/1.00  fof(f5227,plain,(
% 4.20/1.00    ~r2_hidden(sK3,sK5) | (~spl8_1 | ~spl8_8)),
% 4.20/1.00    inference(resolution,[],[f4339,f3133])).
% 4.20/1.00  fof(f3133,plain,(
% 4.20/1.00    r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~spl8_8),
% 4.20/1.00    inference(avatar_component_clause,[],[f3132])).
% 4.20/1.00  fof(f4051,plain,(
% 4.20/1.00    spl8_2 | ~spl8_8 | spl8_11),
% 4.20/1.00    inference(avatar_split_clause,[],[f4050,f4029,f3132,f105])).
% 4.20/1.00  fof(f4050,plain,(
% 4.20/1.00    r2_hidden(sK3,sK5) | (~spl8_8 | spl8_11)),
% 4.20/1.00    inference(subsumption_resolution,[],[f4044,f3133])).
% 4.20/1.00  fof(f4044,plain,(
% 4.20/1.00    r2_hidden(sK3,sK5) | ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_11),
% 4.20/1.00    inference(resolution,[],[f4038,f66])).
% 4.20/1.00  fof(f4038,plain,(
% 4.20/1.00    ~sP0(sK5,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_11),
% 4.20/1.00    inference(resolution,[],[f4031,f132])).
% 4.20/1.00  fof(f4031,plain,(
% 4.20/1.00    ~r2_hidden(sK3,k5_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_11),
% 4.20/1.00    inference(avatar_component_clause,[],[f4029])).
% 4.20/1.00  fof(f3156,plain,(
% 4.20/1.00    spl8_9),
% 4.20/1.00    inference(avatar_contradiction_clause,[],[f3155])).
% 4.20/1.00  fof(f3155,plain,(
% 4.20/1.00    $false | spl8_9),
% 4.20/1.00    inference(subsumption_resolution,[],[f3153,f96])).
% 4.20/1.00  fof(f96,plain,(
% 4.20/1.00    ( ! [X2,X3,X1] : (sP1(X1,X1,X2,X3)) )),
% 4.20/1.00    inference(equality_resolution,[],[f78])).
% 4.20/1.00  fof(f78,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X1) )),
% 4.20/1.00    inference(cnf_transformation,[],[f47])).
% 4.20/1.00  fof(f47,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP1(X0,X1,X2,X3)))),
% 4.20/1.00    inference(rectify,[],[f46])).
% 4.20/1.00  fof(f46,plain,(
% 4.20/1.00    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP1(X4,X2,X1,X0)))),
% 4.20/1.00    inference(flattening,[],[f45])).
% 4.20/1.00  fof(f45,plain,(
% 4.20/1.00    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP1(X4,X2,X1,X0)))),
% 4.20/1.00    inference(nnf_transformation,[],[f29])).
% 4.20/1.00  fof(f3153,plain,(
% 4.20/1.00    ~sP1(sK4,sK4,sK3,sK3) | spl8_9),
% 4.20/1.00    inference(resolution,[],[f3138,f304])).
% 4.20/1.00  fof(f304,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP1(X0,X1,X2,X3)) )),
% 4.20/1.00    inference(resolution,[],[f99,f72])).
% 4.20/1.00  fof(f72,plain,(
% 4.20/1.00    ( ! [X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3) | ~sP1(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 4.20/1.00    inference(cnf_transformation,[],[f44])).
% 4.20/1.00  fof(f44,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ((~sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 4.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 4.20/1.00  fof(f43,plain,(
% 4.20/1.00    ! [X3,X2,X1,X0] : (? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 4.20/1.00    introduced(choice_axiom,[])).
% 4.20/1.00  fof(f42,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 4.20/1.00    inference(rectify,[],[f41])).
% 4.20/1.00  fof(f41,plain,(
% 4.20/1.00    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP1(X4,X2,X1,X0)) & (sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP2(X0,X1,X2,X3)))),
% 4.20/1.00    inference(nnf_transformation,[],[f30])).
% 4.20/1.00  fof(f3138,plain,(
% 4.20/1.00    ~r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_9),
% 4.20/1.00    inference(avatar_component_clause,[],[f3136])).
% 4.20/1.00  fof(f3149,plain,(
% 4.20/1.00    spl8_8),
% 4.20/1.00    inference(avatar_contradiction_clause,[],[f3148])).
% 4.20/1.00  fof(f3148,plain,(
% 4.20/1.00    $false | spl8_8),
% 4.20/1.00    inference(subsumption_resolution,[],[f3146,f97])).
% 4.20/1.00  fof(f97,plain,(
% 4.20/1.00    ( ! [X2,X3,X1] : (sP1(X2,X1,X2,X3)) )),
% 4.20/1.00    inference(equality_resolution,[],[f77])).
% 4.20/1.00  fof(f77,plain,(
% 4.20/1.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X2) )),
% 4.20/1.00    inference(cnf_transformation,[],[f47])).
% 4.20/1.00  fof(f3146,plain,(
% 4.20/1.00    ~sP1(sK3,sK4,sK3,sK3) | spl8_8),
% 4.20/1.00    inference(resolution,[],[f3134,f304])).
% 4.20/1.00  fof(f3134,plain,(
% 4.20/1.00    ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_8),
% 4.20/1.00    inference(avatar_component_clause,[],[f3132])).
% 4.20/1.00  fof(f114,plain,(
% 4.20/1.00    spl8_1 | ~spl8_2),
% 4.20/1.00    inference(avatar_split_clause,[],[f91,f105,f101])).
% 4.20/1.00  fof(f91,plain,(
% 4.20/1.00    ~r2_hidden(sK3,sK5) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 4.20/1.00    inference(definition_unfolding,[],[f49,f88,f57,f88])).
% 4.20/1.00  fof(f49,plain,(
% 4.20/1.00    ~r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5)),
% 4.20/1.00    inference(cnf_transformation,[],[f35])).
% 4.20/1.00  fof(f35,plain,(
% 4.20/1.00    (r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5)) & ((~r2_hidden(sK4,sK5) & ~r2_hidden(sK3,sK5)) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5))),
% 4.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f34])).
% 4.20/1.00  fof(f34,plain,(
% 4.20/1.00    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5)) & ((~r2_hidden(sK4,sK5) & ~r2_hidden(sK3,sK5)) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5)))),
% 4.20/1.00    introduced(choice_axiom,[])).
% 4.20/1.00  fof(f33,plain,(
% 4.20/1.00    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.20/1.00    inference(flattening,[],[f32])).
% 4.20/1.00  fof(f32,plain,(
% 4.20/1.00    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.20/1.00    inference(nnf_transformation,[],[f21])).
% 4.20/1.00  fof(f21,plain,(
% 4.20/1.00    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.20/1.00    inference(ennf_transformation,[],[f18])).
% 4.20/1.00  fof(f18,negated_conjecture,(
% 4.20/1.00    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.20/1.00    inference(negated_conjecture,[],[f17])).
% 4.20/1.00  fof(f17,conjecture,(
% 4.20/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 4.20/1.00  fof(f113,plain,(
% 4.20/1.00    spl8_1 | ~spl8_3),
% 4.20/1.00    inference(avatar_split_clause,[],[f90,f109,f101])).
% 4.20/1.00  fof(f90,plain,(
% 4.20/1.00    ~r2_hidden(sK4,sK5) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 4.20/1.00    inference(definition_unfolding,[],[f50,f88,f57,f88])).
% 4.20/1.00  fof(f50,plain,(
% 4.20/1.00    ~r2_hidden(sK4,sK5) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5)),
% 4.20/1.00    inference(cnf_transformation,[],[f35])).
% 4.20/1.00  fof(f112,plain,(
% 4.20/1.00    ~spl8_1 | spl8_2 | spl8_3),
% 4.20/1.00    inference(avatar_split_clause,[],[f89,f109,f105,f101])).
% 4.20/1.00  fof(f89,plain,(
% 4.20/1.00    r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 4.20/1.00    inference(definition_unfolding,[],[f51,f88,f57,f88])).
% 4.20/1.00  fof(f51,plain,(
% 4.20/1.00    r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5)),
% 4.20/1.00    inference(cnf_transformation,[],[f35])).
% 4.20/1.00  % SZS output end Proof for theBenchmark
% 4.20/1.00  % (7488)------------------------------
% 4.20/1.00  % (7488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/1.00  % (7488)Termination reason: Refutation
% 4.20/1.00  
% 4.20/1.00  % (7488)Memory used [KB]: 9722
% 4.20/1.00  % (7488)Time elapsed: 0.574 s
% 4.20/1.00  % (7488)------------------------------
% 4.20/1.00  % (7488)------------------------------
% 4.20/1.00  % (7460)Success in time 0.634 s
%------------------------------------------------------------------------------
