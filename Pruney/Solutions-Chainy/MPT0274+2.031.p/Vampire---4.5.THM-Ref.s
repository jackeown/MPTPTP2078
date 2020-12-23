%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:24 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 419 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  395 ( 965 expanded)
%              Number of equality atoms :   97 ( 340 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3874,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f115,f2791,f2802,f3104,f3808,f3809,f3829,f3846,f3873])).

fof(f3873,plain,
    ( spl8_3
    | ~ spl8_9
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f3872])).

fof(f3872,plain,
    ( $false
    | spl8_3
    | ~ spl8_9
    | spl8_12 ),
    inference(subsumption_resolution,[],[f3871,f2780])).

fof(f2780,plain,
    ( r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f2779])).

fof(f2779,plain,
    ( spl8_9
  <=> r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f3871,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_3
    | spl8_12 ),
    inference(subsumption_resolution,[],[f3868,f111])).

fof(f111,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_3
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f3868,plain,
    ( r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_12 ),
    inference(resolution,[],[f3861,f66])).

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

fof(f3861,plain,
    ( ~ sP0(sK5,sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_12 ),
    inference(resolution,[],[f3088,f69])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f3088,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f3086])).

fof(f3086,plain,
    ( spl8_12
  <=> r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f3846,plain,
    ( ~ spl8_10
    | spl8_1 ),
    inference(avatar_split_clause,[],[f3841,f102,f2783])).

fof(f2783,plain,
    ( spl8_10
  <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f102,plain,
    ( spl8_1
  <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f3841,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_1 ),
    inference(superposition,[],[f143,f198])).

fof(f198,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f186,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f186,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f62,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f143,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f104,f54])).

fof(f104,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f3829,plain,
    ( ~ spl8_11
    | ~ spl8_12
    | spl8_10 ),
    inference(avatar_split_clause,[],[f3080,f2783,f3086,f3082])).

fof(f3082,plain,
    ( spl8_11
  <=> r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f3080,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_10 ),
    inference(trivial_inequality_removal,[],[f3079])).

fof(f3079,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_10 ),
    inference(superposition,[],[f2785,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f88,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f87])).

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
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f2785,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f2783])).

fof(f3809,plain,
    ( ~ spl8_3
    | ~ spl8_1
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f3800,f2779,f102,f110])).

fof(f3800,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ spl8_1
    | ~ spl8_9 ),
    inference(resolution,[],[f3312,f2780])).

fof(f3312,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
        | ~ r2_hidden(X0,sK5) )
    | ~ spl8_1 ),
    inference(resolution,[],[f3116,f153])).

fof(f153,plain,(
    ! [X4,X2,X3] :
      ( ~ sP0(k3_xboole_0(X3,X2),X4,X2)
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f146,f54])).

fof(f146,plain,(
    ! [X6,X8,X7] :
      ( ~ sP0(k3_xboole_0(X8,X7),X6,X8)
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f122,f69])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f59,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f59,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f3116,plain,
    ( ! [X0] :
        ( sP0(k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
        | ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f68,f3105])).

fof(f3105,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f103,f54])).

fof(f103,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3808,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f3799,f2775,f102,f106])).

fof(f106,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2775,plain,
    ( spl8_8
  <=> r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f3799,plain,
    ( ~ r2_hidden(sK3,sK5)
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(resolution,[],[f3312,f2776])).

fof(f2776,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f2775])).

fof(f3104,plain,
    ( spl8_2
    | ~ spl8_8
    | spl8_11 ),
    inference(avatar_split_clause,[],[f3103,f3082,f2775,f106])).

fof(f3103,plain,
    ( r2_hidden(sK3,sK5)
    | ~ spl8_8
    | spl8_11 ),
    inference(subsumption_resolution,[],[f3097,f2776])).

fof(f3097,plain,
    ( r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_11 ),
    inference(resolution,[],[f3090,f66])).

fof(f3090,plain,
    ( ~ sP0(sK5,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_11 ),
    inference(resolution,[],[f3084,f69])).

fof(f3084,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f3082])).

fof(f2802,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f2801])).

fof(f2801,plain,
    ( $false
    | spl8_9 ),
    inference(subsumption_resolution,[],[f2798,f97])).

fof(f97,plain,(
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

fof(f29,plain,(
    ! [X4,X2,X1,X0] :
      ( sP1(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2798,plain,
    ( ~ sP1(sK4,sK4,sK3,sK3)
    | spl8_9 ),
    inference(resolution,[],[f2781,f275])).

fof(f275,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f100,f72])).

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

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( sP2(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP1(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f100,plain,(
    ! [X2,X0,X1] : sP2(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
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

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f2781,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f2779])).

fof(f2791,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f2790])).

fof(f2790,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f2787,f98])).

fof(f98,plain,(
    ! [X2,X3,X1] : sP1(X2,X1,X2,X3) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2787,plain,
    ( ~ sP1(sK3,sK4,sK3,sK3)
    | spl8_8 ),
    inference(resolution,[],[f2777,f275])).

fof(f2777,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f2775])).

fof(f115,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f91,f106,f102])).

fof(f91,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f49,f88,f56,f88])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f114,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f90,f110,f102])).

fof(f90,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f50,f88,f56,f88])).

fof(f50,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f89,f110,f106,f102])).

fof(f89,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f51,f88,f56,f88])).

fof(f51,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (15080)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15085)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (15084)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (15077)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (15107)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (15102)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (15097)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (15086)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (15082)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (15099)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (15078)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15089)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15094)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (15090)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (15094)Refutation not found, incomplete strategy% (15094)------------------------------
% 0.21/0.52  % (15094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15094)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15094)Memory used [KB]: 10746
% 0.21/0.52  % (15094)Time elapsed: 0.111 s
% 0.21/0.52  % (15094)------------------------------
% 0.21/0.52  % (15094)------------------------------
% 0.21/0.52  % (15100)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (15088)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (15088)Refutation not found, incomplete strategy% (15088)------------------------------
% 0.21/0.52  % (15088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15088)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15088)Memory used [KB]: 10618
% 0.21/0.52  % (15088)Time elapsed: 0.108 s
% 0.21/0.52  % (15088)------------------------------
% 0.21/0.52  % (15088)------------------------------
% 0.21/0.52  % (15085)Refutation not found, incomplete strategy% (15085)------------------------------
% 0.21/0.52  % (15085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15085)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15085)Memory used [KB]: 10618
% 0.21/0.52  % (15085)Time elapsed: 0.108 s
% 0.21/0.52  % (15085)------------------------------
% 0.21/0.52  % (15085)------------------------------
% 0.21/0.52  % (15091)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15079)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15092)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15079)Refutation not found, incomplete strategy% (15079)------------------------------
% 0.21/0.52  % (15079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15101)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (15093)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15098)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (15104)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (15083)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (15087)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (15081)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15087)Refutation not found, incomplete strategy% (15087)------------------------------
% 0.21/0.53  % (15087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15087)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15087)Memory used [KB]: 10618
% 0.21/0.53  % (15087)Time elapsed: 0.117 s
% 0.21/0.53  % (15087)------------------------------
% 0.21/0.53  % (15087)------------------------------
% 0.21/0.53  % (15106)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (15105)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15103)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15095)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (15079)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15079)Memory used [KB]: 10746
% 0.21/0.54  % (15079)Time elapsed: 0.106 s
% 0.21/0.54  % (15079)------------------------------
% 0.21/0.54  % (15079)------------------------------
% 1.97/0.64  % (15153)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.97/0.64  % (15154)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.97/0.66  % (15146)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.20/0.67  % (15145)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.20/0.67  % (15150)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.95/0.80  % (15105)Refutation found. Thanks to Tanya!
% 2.95/0.80  % SZS status Theorem for theBenchmark
% 2.95/0.80  % SZS output start Proof for theBenchmark
% 2.95/0.80  fof(f3874,plain,(
% 2.95/0.80    $false),
% 2.95/0.80    inference(avatar_sat_refutation,[],[f113,f114,f115,f2791,f2802,f3104,f3808,f3809,f3829,f3846,f3873])).
% 2.95/0.80  fof(f3873,plain,(
% 2.95/0.80    spl8_3 | ~spl8_9 | spl8_12),
% 2.95/0.80    inference(avatar_contradiction_clause,[],[f3872])).
% 2.95/0.80  fof(f3872,plain,(
% 2.95/0.80    $false | (spl8_3 | ~spl8_9 | spl8_12)),
% 2.95/0.80    inference(subsumption_resolution,[],[f3871,f2780])).
% 2.95/0.80  fof(f2780,plain,(
% 2.95/0.80    r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~spl8_9),
% 2.95/0.80    inference(avatar_component_clause,[],[f2779])).
% 2.95/0.80  fof(f2779,plain,(
% 2.95/0.80    spl8_9 <=> r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.95/0.80  fof(f3871,plain,(
% 2.95/0.80    ~r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | (spl8_3 | spl8_12)),
% 2.95/0.80    inference(subsumption_resolution,[],[f3868,f111])).
% 2.95/0.80  fof(f111,plain,(
% 2.95/0.80    ~r2_hidden(sK4,sK5) | spl8_3),
% 2.95/0.80    inference(avatar_component_clause,[],[f110])).
% 2.95/0.80  fof(f110,plain,(
% 2.95/0.80    spl8_3 <=> r2_hidden(sK4,sK5)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.95/0.80  fof(f3868,plain,(
% 2.95/0.80    r2_hidden(sK4,sK5) | ~r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_12),
% 2.95/0.80    inference(resolution,[],[f3861,f66])).
% 2.95/0.80  fof(f66,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f39])).
% 2.95/0.80  fof(f39,plain,(
% 2.95/0.80    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 2.95/0.80    inference(rectify,[],[f38])).
% 2.95/0.80  fof(f38,plain,(
% 2.95/0.80    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 2.95/0.80    inference(nnf_transformation,[],[f27])).
% 2.95/0.80  fof(f27,plain,(
% 2.95/0.80    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.95/0.80    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.95/0.80  fof(f3861,plain,(
% 2.95/0.80    ~sP0(sK5,sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_12),
% 2.95/0.80    inference(resolution,[],[f3088,f69])).
% 2.95/0.80  fof(f69,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f40])).
% 2.95/0.80  fof(f40,plain,(
% 2.95/0.80    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.95/0.80    inference(nnf_transformation,[],[f28])).
% 2.95/0.80  fof(f28,plain,(
% 2.95/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 2.95/0.80    inference(definition_folding,[],[f25,f27])).
% 2.95/0.80  fof(f25,plain,(
% 2.95/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.95/0.80    inference(ennf_transformation,[],[f3])).
% 2.95/0.80  fof(f3,axiom,(
% 2.95/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.95/0.80  fof(f3088,plain,(
% 2.95/0.80    ~r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_12),
% 2.95/0.80    inference(avatar_component_clause,[],[f3086])).
% 2.95/0.80  fof(f3086,plain,(
% 2.95/0.80    spl8_12 <=> r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 2.95/0.80  fof(f3846,plain,(
% 2.95/0.80    ~spl8_10 | spl8_1),
% 2.95/0.80    inference(avatar_split_clause,[],[f3841,f102,f2783])).
% 2.95/0.80  fof(f2783,plain,(
% 2.95/0.80    spl8_10 <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.95/0.80  fof(f102,plain,(
% 2.95/0.80    spl8_1 <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.95/0.80  fof(f3841,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_1),
% 2.95/0.80    inference(superposition,[],[f143,f198])).
% 2.95/0.80  fof(f198,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.95/0.80    inference(forward_demodulation,[],[f186,f54])).
% 2.95/0.80  fof(f54,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f1])).
% 2.95/0.80  fof(f1,axiom,(
% 2.95/0.80    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.95/0.80  fof(f186,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.95/0.80    inference(superposition,[],[f62,f52])).
% 2.95/0.80  fof(f52,plain,(
% 2.95/0.80    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.95/0.80    inference(cnf_transformation,[],[f19])).
% 2.95/0.80  fof(f19,plain,(
% 2.95/0.80    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.95/0.80    inference(rectify,[],[f2])).
% 2.95/0.80  fof(f2,axiom,(
% 2.95/0.80    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.95/0.80  fof(f62,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f6])).
% 2.95/0.80  fof(f6,axiom,(
% 2.95/0.80    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.95/0.80  fof(f143,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | spl8_1),
% 2.95/0.80    inference(forward_demodulation,[],[f104,f54])).
% 2.95/0.80  fof(f104,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_1),
% 2.95/0.80    inference(avatar_component_clause,[],[f102])).
% 2.95/0.80  fof(f3829,plain,(
% 2.95/0.80    ~spl8_11 | ~spl8_12 | spl8_10),
% 2.95/0.80    inference(avatar_split_clause,[],[f3080,f2783,f3086,f3082])).
% 2.95/0.80  fof(f3082,plain,(
% 2.95/0.80    spl8_11 <=> r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 2.95/0.80  fof(f3080,plain,(
% 2.95/0.80    ~r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | ~r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_10),
% 2.95/0.80    inference(trivial_inequality_removal,[],[f3079])).
% 2.95/0.80  fof(f3079,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | ~r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | ~r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_10),
% 2.95/0.80    inference(superposition,[],[f2785,f94])).
% 2.95/0.80  fof(f94,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f63,f88,f88])).
% 2.95/0.80  fof(f88,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f55,f87])).
% 2.95/0.80  fof(f87,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f61,f86])).
% 2.95/0.80  fof(f86,plain,(
% 2.95/0.80    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f70,f85])).
% 2.95/0.80  fof(f85,plain,(
% 2.95/0.80    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f81,f84])).
% 2.95/0.80  fof(f84,plain,(
% 2.95/0.80    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f82,f83])).
% 2.95/0.80  fof(f83,plain,(
% 2.95/0.80    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f14])).
% 2.95/0.80  fof(f14,axiom,(
% 2.95/0.80    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.95/0.80  fof(f82,plain,(
% 2.95/0.80    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f13])).
% 2.95/0.80  fof(f13,axiom,(
% 2.95/0.80    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.95/0.80  fof(f81,plain,(
% 2.95/0.80    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f12])).
% 2.95/0.80  fof(f12,axiom,(
% 2.95/0.80    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.95/0.80  fof(f70,plain,(
% 2.95/0.80    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f11])).
% 2.95/0.80  fof(f11,axiom,(
% 2.95/0.80    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.95/0.80  fof(f61,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f10])).
% 2.95/0.80  fof(f10,axiom,(
% 2.95/0.80    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.95/0.80  fof(f55,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f9])).
% 2.95/0.80  fof(f9,axiom,(
% 2.95/0.80    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.95/0.80  fof(f63,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f24])).
% 2.95/0.80  fof(f24,plain,(
% 2.95/0.80    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.95/0.80    inference(flattening,[],[f23])).
% 2.95/0.80  fof(f23,plain,(
% 2.95/0.80    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.95/0.80    inference(ennf_transformation,[],[f16])).
% 2.95/0.80  fof(f16,axiom,(
% 2.95/0.80    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.95/0.80  fof(f2785,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_10),
% 2.95/0.80    inference(avatar_component_clause,[],[f2783])).
% 2.95/0.80  fof(f3809,plain,(
% 2.95/0.80    ~spl8_3 | ~spl8_1 | ~spl8_9),
% 2.95/0.80    inference(avatar_split_clause,[],[f3800,f2779,f102,f110])).
% 2.95/0.80  fof(f3800,plain,(
% 2.95/0.80    ~r2_hidden(sK4,sK5) | (~spl8_1 | ~spl8_9)),
% 2.95/0.80    inference(resolution,[],[f3312,f2780])).
% 2.95/0.80  fof(f3312,plain,(
% 2.95/0.80    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~r2_hidden(X0,sK5)) ) | ~spl8_1),
% 2.95/0.80    inference(resolution,[],[f3116,f153])).
% 2.95/0.80  fof(f153,plain,(
% 2.95/0.80    ( ! [X4,X2,X3] : (~sP0(k3_xboole_0(X3,X2),X4,X2) | ~r2_hidden(X4,X3)) )),
% 2.95/0.80    inference(superposition,[],[f146,f54])).
% 2.95/0.80  fof(f146,plain,(
% 2.95/0.80    ( ! [X6,X8,X7] : (~sP0(k3_xboole_0(X8,X7),X6,X8) | ~r2_hidden(X6,X7)) )),
% 2.95/0.80    inference(resolution,[],[f122,f69])).
% 2.95/0.80  fof(f122,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r2_hidden(X0,X1)) )),
% 2.95/0.80    inference(resolution,[],[f59,f92])).
% 2.95/0.80  fof(f92,plain,(
% 2.95/0.80    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.95/0.80    inference(definition_unfolding,[],[f53,f56])).
% 2.95/0.80  fof(f56,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.95/0.80    inference(cnf_transformation,[],[f5])).
% 2.95/0.80  fof(f5,axiom,(
% 2.95/0.80    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.95/0.80  fof(f53,plain,(
% 2.95/0.80    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f7])).
% 2.95/0.80  fof(f7,axiom,(
% 2.95/0.80    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.95/0.80  fof(f59,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f37])).
% 2.95/0.80  fof(f37,plain,(
% 2.95/0.80    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.95/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f36])).
% 2.95/0.80  fof(f36,plain,(
% 2.95/0.80    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 2.95/0.80    introduced(choice_axiom,[])).
% 2.95/0.80  fof(f22,plain,(
% 2.95/0.80    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.95/0.80    inference(ennf_transformation,[],[f20])).
% 2.95/0.80  fof(f20,plain,(
% 2.95/0.80    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.95/0.80    inference(rectify,[],[f4])).
% 2.95/0.80  fof(f4,axiom,(
% 2.95/0.80    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.95/0.80  fof(f3116,plain,(
% 2.95/0.80    ( ! [X0] : (sP0(k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ) | ~spl8_1),
% 2.95/0.80    inference(superposition,[],[f68,f3105])).
% 2.95/0.80  fof(f3105,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) | ~spl8_1),
% 2.95/0.80    inference(forward_demodulation,[],[f103,f54])).
% 2.95/0.80  fof(f103,plain,(
% 2.95/0.80    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | ~spl8_1),
% 2.95/0.80    inference(avatar_component_clause,[],[f102])).
% 2.95/0.80  fof(f68,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f40])).
% 2.95/0.80  fof(f3808,plain,(
% 2.95/0.80    ~spl8_2 | ~spl8_1 | ~spl8_8),
% 2.95/0.80    inference(avatar_split_clause,[],[f3799,f2775,f102,f106])).
% 2.95/0.80  fof(f106,plain,(
% 2.95/0.80    spl8_2 <=> r2_hidden(sK3,sK5)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.95/0.80  fof(f2775,plain,(
% 2.95/0.80    spl8_8 <=> r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.95/0.80  fof(f3799,plain,(
% 2.95/0.80    ~r2_hidden(sK3,sK5) | (~spl8_1 | ~spl8_8)),
% 2.95/0.80    inference(resolution,[],[f3312,f2776])).
% 2.95/0.80  fof(f2776,plain,(
% 2.95/0.80    r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~spl8_8),
% 2.95/0.80    inference(avatar_component_clause,[],[f2775])).
% 2.95/0.80  fof(f3104,plain,(
% 2.95/0.80    spl8_2 | ~spl8_8 | spl8_11),
% 2.95/0.80    inference(avatar_split_clause,[],[f3103,f3082,f2775,f106])).
% 2.95/0.80  fof(f3103,plain,(
% 2.95/0.80    r2_hidden(sK3,sK5) | (~spl8_8 | spl8_11)),
% 2.95/0.80    inference(subsumption_resolution,[],[f3097,f2776])).
% 2.95/0.80  fof(f3097,plain,(
% 2.95/0.80    r2_hidden(sK3,sK5) | ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_11),
% 2.95/0.80    inference(resolution,[],[f3090,f66])).
% 2.95/0.80  fof(f3090,plain,(
% 2.95/0.80    ~sP0(sK5,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_11),
% 2.95/0.80    inference(resolution,[],[f3084,f69])).
% 2.95/0.80  fof(f3084,plain,(
% 2.95/0.80    ~r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) | spl8_11),
% 2.95/0.80    inference(avatar_component_clause,[],[f3082])).
% 2.95/0.80  fof(f2802,plain,(
% 2.95/0.80    spl8_9),
% 2.95/0.80    inference(avatar_contradiction_clause,[],[f2801])).
% 2.95/0.80  fof(f2801,plain,(
% 2.95/0.80    $false | spl8_9),
% 2.95/0.80    inference(subsumption_resolution,[],[f2798,f97])).
% 2.95/0.80  fof(f97,plain,(
% 2.95/0.80    ( ! [X2,X3,X1] : (sP1(X1,X1,X2,X3)) )),
% 2.95/0.80    inference(equality_resolution,[],[f78])).
% 2.95/0.80  fof(f78,plain,(
% 2.95/0.80    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X1) )),
% 2.95/0.80    inference(cnf_transformation,[],[f47])).
% 2.95/0.80  fof(f47,plain,(
% 2.95/0.80    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP1(X0,X1,X2,X3)))),
% 2.95/0.80    inference(rectify,[],[f46])).
% 2.95/0.80  fof(f46,plain,(
% 2.95/0.80    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP1(X4,X2,X1,X0)))),
% 2.95/0.80    inference(flattening,[],[f45])).
% 2.95/0.80  fof(f45,plain,(
% 2.95/0.80    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP1(X4,X2,X1,X0)))),
% 2.95/0.80    inference(nnf_transformation,[],[f29])).
% 2.95/0.80  fof(f29,plain,(
% 2.95/0.80    ! [X4,X2,X1,X0] : (sP1(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 2.95/0.80    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.95/0.80  fof(f2798,plain,(
% 2.95/0.80    ~sP1(sK4,sK4,sK3,sK3) | spl8_9),
% 2.95/0.80    inference(resolution,[],[f2781,f275])).
% 2.95/0.80  fof(f275,plain,(
% 2.95/0.80    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP1(X0,X1,X2,X3)) )),
% 2.95/0.80    inference(resolution,[],[f100,f72])).
% 2.95/0.80  fof(f72,plain,(
% 2.95/0.80    ( ! [X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3) | ~sP1(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f44])).
% 2.95/0.80  fof(f44,plain,(
% 2.95/0.80    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ((~sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 2.95/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 2.95/0.83  fof(f43,plain,(
% 2.95/0.83    ! [X3,X2,X1,X0] : (? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP1(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 2.95/0.83    introduced(choice_axiom,[])).
% 2.95/0.83  fof(f42,plain,(
% 2.95/0.83    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 2.95/0.83    inference(rectify,[],[f41])).
% 2.95/0.83  fof(f41,plain,(
% 2.95/0.83    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP1(X4,X2,X1,X0)) & (sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP2(X0,X1,X2,X3)))),
% 2.95/0.83    inference(nnf_transformation,[],[f30])).
% 2.95/0.83  fof(f30,plain,(
% 2.95/0.83    ! [X0,X1,X2,X3] : (sP2(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP1(X4,X2,X1,X0)))),
% 2.95/0.83    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.95/0.83  fof(f100,plain,(
% 2.95/0.83    ( ! [X2,X0,X1] : (sP2(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 2.95/0.83    inference(equality_resolution,[],[f96])).
% 2.95/0.83  fof(f96,plain,(
% 2.95/0.83    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.95/0.83    inference(definition_unfolding,[],[f79,f87])).
% 2.95/0.83  fof(f79,plain,(
% 2.95/0.83    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.95/0.83    inference(cnf_transformation,[],[f48])).
% 2.95/0.83  fof(f48,plain,(
% 2.95/0.83    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP2(X0,X1,X2,X3)) & (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 2.95/0.83    inference(nnf_transformation,[],[f31])).
% 2.95/0.83  fof(f31,plain,(
% 2.95/0.83    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP2(X0,X1,X2,X3))),
% 2.95/0.83    inference(definition_folding,[],[f26,f30,f29])).
% 2.95/0.83  fof(f26,plain,(
% 2.95/0.83    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.95/0.83    inference(ennf_transformation,[],[f8])).
% 2.95/0.83  fof(f8,axiom,(
% 2.95/0.83    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.95/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.95/0.83  fof(f2781,plain,(
% 2.95/0.83    ~r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_9),
% 2.95/0.83    inference(avatar_component_clause,[],[f2779])).
% 2.95/0.83  fof(f2791,plain,(
% 2.95/0.83    spl8_8),
% 2.95/0.83    inference(avatar_contradiction_clause,[],[f2790])).
% 2.95/0.83  fof(f2790,plain,(
% 2.95/0.83    $false | spl8_8),
% 2.95/0.83    inference(subsumption_resolution,[],[f2787,f98])).
% 2.95/0.83  fof(f98,plain,(
% 2.95/0.83    ( ! [X2,X3,X1] : (sP1(X2,X1,X2,X3)) )),
% 2.95/0.83    inference(equality_resolution,[],[f77])).
% 2.95/0.83  fof(f77,plain,(
% 2.95/0.83    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X2) )),
% 2.95/0.83    inference(cnf_transformation,[],[f47])).
% 2.95/0.83  fof(f2787,plain,(
% 2.95/0.83    ~sP1(sK3,sK4,sK3,sK3) | spl8_8),
% 2.95/0.83    inference(resolution,[],[f2777,f275])).
% 2.95/0.83  fof(f2777,plain,(
% 2.95/0.83    ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_8),
% 2.95/0.83    inference(avatar_component_clause,[],[f2775])).
% 2.95/0.83  fof(f115,plain,(
% 2.95/0.83    spl8_1 | ~spl8_2),
% 2.95/0.83    inference(avatar_split_clause,[],[f91,f106,f102])).
% 2.95/0.83  fof(f91,plain,(
% 2.95/0.83    ~r2_hidden(sK3,sK5) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.83    inference(definition_unfolding,[],[f49,f88,f56,f88])).
% 2.95/0.83  fof(f49,plain,(
% 2.95/0.83    ~r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5)),
% 2.95/0.83    inference(cnf_transformation,[],[f35])).
% 2.95/0.83  fof(f35,plain,(
% 2.95/0.83    (r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5)) & ((~r2_hidden(sK4,sK5) & ~r2_hidden(sK3,sK5)) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5))),
% 2.95/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f34])).
% 2.95/0.83  fof(f34,plain,(
% 2.95/0.83    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5)) & ((~r2_hidden(sK4,sK5) & ~r2_hidden(sK3,sK5)) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5)))),
% 2.95/0.83    introduced(choice_axiom,[])).
% 2.95/0.83  fof(f33,plain,(
% 2.95/0.83    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.95/0.83    inference(flattening,[],[f32])).
% 2.95/0.83  fof(f32,plain,(
% 2.95/0.83    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.95/0.83    inference(nnf_transformation,[],[f21])).
% 2.95/0.83  fof(f21,plain,(
% 2.95/0.83    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.95/0.83    inference(ennf_transformation,[],[f18])).
% 2.95/0.83  fof(f18,negated_conjecture,(
% 2.95/0.83    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.95/0.83    inference(negated_conjecture,[],[f17])).
% 2.95/0.83  fof(f17,conjecture,(
% 2.95/0.83    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.95/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.95/0.83  fof(f114,plain,(
% 2.95/0.83    spl8_1 | ~spl8_3),
% 2.95/0.83    inference(avatar_split_clause,[],[f90,f110,f102])).
% 2.95/0.83  fof(f90,plain,(
% 2.95/0.83    ~r2_hidden(sK4,sK5) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.83    inference(definition_unfolding,[],[f50,f88,f56,f88])).
% 2.95/0.83  fof(f50,plain,(
% 2.95/0.83    ~r2_hidden(sK4,sK5) | k2_tarski(sK3,sK4) = k4_xboole_0(k2_tarski(sK3,sK4),sK5)),
% 2.95/0.83    inference(cnf_transformation,[],[f35])).
% 2.95/0.83  fof(f113,plain,(
% 2.95/0.83    ~spl8_1 | spl8_2 | spl8_3),
% 2.95/0.83    inference(avatar_split_clause,[],[f89,f110,f106,f102])).
% 2.95/0.83  fof(f89,plain,(
% 2.95/0.83    r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5))),
% 2.95/0.83    inference(definition_unfolding,[],[f51,f88,f56,f88])).
% 2.95/0.83  fof(f51,plain,(
% 2.95/0.83    r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k2_tarski(sK3,sK4) != k4_xboole_0(k2_tarski(sK3,sK4),sK5)),
% 2.95/0.83    inference(cnf_transformation,[],[f35])).
% 2.95/0.83  % SZS output end Proof for theBenchmark
% 2.95/0.83  % (15105)------------------------------
% 2.95/0.83  % (15105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.83  % (15105)Termination reason: Refutation
% 2.95/0.83  
% 2.95/0.83  % (15105)Memory used [KB]: 8315
% 2.95/0.83  % (15105)Time elapsed: 0.403 s
% 2.95/0.83  % (15105)------------------------------
% 2.95/0.83  % (15105)------------------------------
% 2.95/0.83  % (15076)Success in time 0.465 s
%------------------------------------------------------------------------------
