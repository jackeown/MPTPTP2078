%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:23 EST 2020

% Result     : Theorem 6.82s
% Output     : Refutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 620 expanded)
%              Number of leaves         :   32 ( 207 expanded)
%              Depth                    :   16
%              Number of atoms          :  491 (1513 expanded)
%              Number of equality atoms :  107 ( 543 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f124,f125,f2550,f2557,f4210,f5734,f5735,f5767,f5819,f6148])).

fof(f6148,plain,
    ( spl10_3
    | ~ spl10_11
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f6147])).

fof(f6147,plain,
    ( $false
    | spl10_3
    | ~ spl10_11
    | spl10_16 ),
    inference(subsumption_resolution,[],[f6146,f2539])).

fof(f2539,plain,
    ( r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f2538])).

fof(f2538,plain,
    ( spl10_11
  <=> r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f6146,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_3
    | spl10_16 ),
    inference(subsumption_resolution,[],[f6143,f121])).

fof(f121,plain,
    ( ~ r2_hidden(sK6,sK7)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl10_3
  <=> r2_hidden(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f6143,plain,
    ( r2_hidden(sK6,sK7)
    | ~ r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_16 ),
    inference(resolution,[],[f6138,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f6138,plain,
    ( ~ sP2(sK7,sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_16 ),
    inference(resolution,[],[f4196,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X1,X0))
      | ~ sP2(X1,X2,X0) ) ),
    inference(superposition,[],[f80,f59])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
      & ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP2(X2,X0,X1) ) ),
    inference(definition_folding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f4196,plain,
    ( ~ r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_16 ),
    inference(avatar_component_clause,[],[f4194])).

fof(f4194,plain,
    ( spl10_16
  <=> r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f5819,plain,
    ( ~ spl10_12
    | spl10_1 ),
    inference(avatar_split_clause,[],[f5818,f112,f2542])).

fof(f2542,plain,
    ( spl10_12
  <=> k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f112,plain,
    ( spl10_1
  <=> k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f5818,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_1 ),
    inference(forward_demodulation,[],[f5811,f59])).

fof(f5811,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))
    | spl10_1 ),
    inference(superposition,[],[f216,f253])).

fof(f253,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f235,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f235,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f64,f58])).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f216,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_1 ),
    inference(forward_demodulation,[],[f114,f60])).

fof(f114,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f5767,plain,
    ( ~ spl10_15
    | ~ spl10_16
    | spl10_12 ),
    inference(avatar_split_clause,[],[f4188,f2542,f4194,f4190])).

fof(f4190,plain,
    ( spl10_15
  <=> r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f4188,plain,
    ( ~ r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | ~ r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_12 ),
    inference(trivial_inequality_removal,[],[f4185])).

fof(f4185,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | ~ r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | ~ r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_12 ),
    inference(superposition,[],[f2544,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f99,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f81,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f92,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f93,f94])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f2544,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f2542])).

fof(f5735,plain,
    ( ~ spl10_3
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f5725,f2538,f112,f120])).

fof(f5725,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(resolution,[],[f4779,f2539])).

fof(f4779,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
        | ~ r2_hidden(X1,sK7) )
    | ~ spl10_1 ),
    inference(resolution,[],[f4676,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4676,plain,
    ( ! [X0] : ~ sP0(sK7,X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | ~ spl10_1 ),
    inference(resolution,[],[f4675,f187])).

fof(f187,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X4,k3_xboole_0(X3,X5))
      | ~ sP0(X3,X4,X5) ) ),
    inference(resolution,[],[f67,f127])).

fof(f127,plain,(
    ! [X2,X1] : sP1(X1,X2,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f106,f60])).

fof(f106,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP0(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP0(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f4675,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | ~ spl10_1 ),
    inference(resolution,[],[f4674,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] : sP4(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f90,f98])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP4(X0,X1,X2,X3) )
      & ( sP4(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP4(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f23,f30,f29])).

fof(f29,plain,(
    ! [X4,X2,X1,X0] :
      ( sP3(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( sP4(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP3(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f23,plain,(
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

fof(f4674,plain,
    ( ! [X4,X3] :
        ( ~ sP4(sK5,sK5,sK6,X4)
        | ~ r2_hidden(X3,k3_xboole_0(sK7,X4)) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f4672,f4655])).

fof(f4655,plain,
    ( ! [X2,X1] :
        ( ~ sP4(sK5,sK5,sK6,X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X1,k3_xboole_0(sK7,X2)) )
    | ~ spl10_1 ),
    inference(duplicate_literal_removal,[],[f4644])).

fof(f4644,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ sP4(sK5,sK5,sK6,X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X1,k3_xboole_0(sK7,X2)) )
    | ~ spl10_1 ),
    inference(resolution,[],[f4583,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4583,plain,
    ( ! [X0,X1] :
        ( sP2(k3_xboole_0(sK7,X0),X1,X0)
        | ~ r2_hidden(X1,X0)
        | ~ sP4(sK5,sK5,sK6,X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f4241,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f91,f98])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4241,plain,
    ( ! [X1] :
        ( sP2(k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),X1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
        | ~ r2_hidden(X1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) )
    | ~ spl10_1 ),
    inference(superposition,[],[f79,f4211])).

fof(f4211,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f113,f60])).

fof(f113,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4672,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X3,X4)
        | ~ sP4(sK5,sK5,sK6,X4)
        | ~ r2_hidden(X3,k3_xboole_0(sK7,X4)) )
    | ~ spl10_1 ),
    inference(duplicate_literal_removal,[],[f4660])).

fof(f4660,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X3,X4)
        | ~ sP4(sK5,sK5,sK6,X4)
        | r2_hidden(X3,X4)
        | ~ r2_hidden(X3,k3_xboole_0(sK7,X4)) )
    | ~ spl10_1 ),
    inference(resolution,[],[f4640,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4640,plain,
    ( ! [X0,X1] :
        ( ~ sP2(k3_xboole_0(sK7,X0),X1,X0)
        | r2_hidden(X1,X0)
        | ~ sP4(sK5,sK5,sK6,X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f4242,f104])).

fof(f4242,plain,
    ( ! [X2] :
        ( ~ sP2(k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),X2,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
        | r2_hidden(X2,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) )
    | ~ spl10_1 ),
    inference(superposition,[],[f80,f4211])).

fof(f5734,plain,
    ( ~ spl10_2
    | ~ spl10_1
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f5724,f2534,f112,f116])).

fof(f116,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2534,plain,
    ( spl10_10
  <=> r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f5724,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ spl10_1
    | ~ spl10_10 ),
    inference(resolution,[],[f4779,f2535])).

fof(f2535,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f2534])).

fof(f4210,plain,
    ( spl10_2
    | ~ spl10_10
    | spl10_15 ),
    inference(avatar_split_clause,[],[f4209,f4190,f2534,f116])).

fof(f4209,plain,
    ( r2_hidden(sK5,sK7)
    | ~ spl10_10
    | spl10_15 ),
    inference(subsumption_resolution,[],[f4203,f2535])).

fof(f4203,plain,
    ( r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_15 ),
    inference(resolution,[],[f4198,f77])).

fof(f4198,plain,
    ( ~ sP2(sK7,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_15 ),
    inference(resolution,[],[f4192,f148])).

fof(f4192,plain,
    ( ~ r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f4190])).

fof(f2557,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f2556])).

fof(f2556,plain,
    ( $false
    | spl10_11 ),
    inference(subsumption_resolution,[],[f2554,f107])).

fof(f107,plain,(
    ! [X2,X3,X1] : sP3(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f2554,plain,
    ( ~ sP3(sK6,sK6,sK5,sK5)
    | spl10_11 ),
    inference(resolution,[],[f2540,f404])).

fof(f404,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f110,f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ sP3(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
          & ( sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP3(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP3(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
        & ( sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP3(X4,X2,X1,X0) )
            & ( sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f2540,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_11 ),
    inference(avatar_component_clause,[],[f2538])).

fof(f2550,plain,(
    spl10_10 ),
    inference(avatar_contradiction_clause,[],[f2549])).

fof(f2549,plain,
    ( $false
    | spl10_10 ),
    inference(subsumption_resolution,[],[f2547,f108])).

fof(f108,plain,(
    ! [X2,X3,X1] : sP3(X2,X1,X2,X3) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2547,plain,
    ( ~ sP3(sK5,sK6,sK5,sK5)
    | spl10_10 ),
    inference(resolution,[],[f2536,f404])).

fof(f2536,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f2534])).

fof(f125,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f102,f116,f112])).

fof(f102,plain,
    ( ~ r2_hidden(sK5,sK7)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f55,f99,f62,f99])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,
    ( ~ r2_hidden(sK5,sK7)
    | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( r2_hidden(sK6,sK7)
      | r2_hidden(sK5,sK7)
      | k2_tarski(sK5,sK6) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) )
    & ( ( ~ r2_hidden(sK6,sK7)
        & ~ r2_hidden(sK5,sK7) )
      | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK6,sK7)
        | r2_hidden(sK5,sK7)
        | k2_tarski(sK5,sK6) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) )
      & ( ( ~ r2_hidden(sK6,sK7)
          & ~ r2_hidden(sK5,sK7) )
        | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ) ) ),
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f124,plain,
    ( spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f101,f120,f112])).

fof(f101,plain,
    ( ~ r2_hidden(sK6,sK7)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f56,f99,f62,f99])).

fof(f56,plain,
    ( ~ r2_hidden(sK6,sK7)
    | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f100,f120,f116,f112])).

fof(f100,plain,
    ( r2_hidden(sK6,sK7)
    | r2_hidden(sK5,sK7)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f57,f99,f62,f99])).

fof(f57,plain,
    ( r2_hidden(sK6,sK7)
    | r2_hidden(sK5,sK7)
    | k2_tarski(sK5,sK6) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (14234)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (14235)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (14237)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (14235)Refutation not found, incomplete strategy% (14235)------------------------------
% 0.21/0.56  % (14235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14235)Memory used [KB]: 10746
% 0.21/0.56  % (14235)Time elapsed: 0.122 s
% 0.21/0.56  % (14235)------------------------------
% 0.21/0.56  % (14235)------------------------------
% 0.21/0.56  % (14242)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (14233)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (14253)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.57  % (14249)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.57  % (14251)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.57  % (14243)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.57  % (14241)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.54/0.58  % (14245)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.58  % (14250)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.72/0.59  % (14230)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.72/0.59  % (14226)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.72/0.59  % (14252)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.72/0.59  % (14229)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.72/0.60  % (14255)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.72/0.60  % (14238)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.72/0.60  % (14236)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.72/0.60  % (14244)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.72/0.60  % (14229)Refutation not found, incomplete strategy% (14229)------------------------------
% 1.72/0.60  % (14229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (14244)Refutation not found, incomplete strategy% (14244)------------------------------
% 1.72/0.60  % (14244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (14244)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (14244)Memory used [KB]: 10746
% 1.72/0.60  % (14244)Time elapsed: 0.130 s
% 1.72/0.60  % (14244)------------------------------
% 1.72/0.60  % (14244)------------------------------
% 1.72/0.60  % (14246)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.72/0.61  % (14228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.72/0.61  % (14256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.72/0.61  % (14247)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.72/0.61  % (14248)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.72/0.61  % (14229)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (14229)Memory used [KB]: 10746
% 1.72/0.61  % (14229)Time elapsed: 0.136 s
% 1.72/0.61  % (14229)------------------------------
% 1.72/0.61  % (14229)------------------------------
% 1.72/0.61  % (14231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.72/0.61  % (14232)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.72/0.61  % (14239)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.72/0.61  % (14254)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.72/0.61  % (14240)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.23/0.69  % (14260)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.63/0.74  % (14264)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.90/0.76  % (14267)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.53/0.85  % (14232)Time limit reached!
% 3.53/0.85  % (14232)------------------------------
% 3.53/0.85  % (14232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.86  % (14232)Termination reason: Time limit
% 3.53/0.86  
% 3.53/0.86  % (14232)Memory used [KB]: 8315
% 3.53/0.86  % (14232)Time elapsed: 0.423 s
% 3.53/0.86  % (14232)------------------------------
% 3.53/0.86  % (14232)------------------------------
% 3.87/0.94  % (14239)Time limit reached!
% 3.87/0.94  % (14239)------------------------------
% 3.87/0.94  % (14239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.94  % (14239)Termination reason: Time limit
% 4.27/0.94  
% 4.27/0.94  % (14239)Memory used [KB]: 9210
% 4.27/0.94  % (14239)Time elapsed: 0.518 s
% 4.27/0.94  % (14239)------------------------------
% 4.27/0.94  % (14239)------------------------------
% 4.27/0.95  % (14226)Time limit reached!
% 4.27/0.95  % (14226)------------------------------
% 4.27/0.95  % (14226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.95  % (14226)Termination reason: Time limit
% 4.27/0.95  % (14226)Termination phase: Saturation
% 4.27/0.95  
% 4.27/0.95  % (14226)Memory used [KB]: 2430
% 4.27/0.95  % (14226)Time elapsed: 0.500 s
% 4.27/0.95  % (14226)------------------------------
% 4.27/0.95  % (14226)------------------------------
% 4.27/0.95  % (14237)Time limit reached!
% 4.27/0.95  % (14237)------------------------------
% 4.27/0.95  % (14237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.95  % (14237)Termination reason: Time limit
% 4.27/0.95  
% 4.27/0.95  % (14237)Memory used [KB]: 15095
% 4.27/0.95  % (14237)Time elapsed: 0.515 s
% 4.27/0.95  % (14237)------------------------------
% 4.27/0.95  % (14237)------------------------------
% 4.39/0.96  % (14228)Time limit reached!
% 4.39/0.96  % (14228)------------------------------
% 4.39/0.96  % (14228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.96  % (14228)Termination reason: Time limit
% 4.39/0.96  
% 4.39/0.96  % (14228)Memory used [KB]: 8443
% 4.39/0.96  % (14228)Time elapsed: 0.515 s
% 4.39/0.96  % (14228)------------------------------
% 4.39/0.96  % (14228)------------------------------
% 4.39/0.99  % (14400)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.71/1.04  % (14255)Time limit reached!
% 4.71/1.04  % (14255)------------------------------
% 4.71/1.04  % (14255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.04  % (14255)Termination reason: Time limit
% 4.71/1.04  
% 4.71/1.04  % (14255)Memory used [KB]: 9210
% 4.71/1.04  % (14255)Time elapsed: 0.614 s
% 4.71/1.04  % (14255)------------------------------
% 4.71/1.04  % (14255)------------------------------
% 4.71/1.06  % (14420)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.46/1.07  % (14418)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.46/1.07  % (14243)Time limit reached!
% 5.46/1.07  % (14243)------------------------------
% 5.46/1.07  % (14243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.46/1.07  % (14243)Termination reason: Time limit
% 5.46/1.07  
% 5.46/1.07  % (14243)Memory used [KB]: 16886
% 5.46/1.07  % (14243)Time elapsed: 0.626 s
% 5.46/1.07  % (14243)------------------------------
% 5.46/1.07  % (14243)------------------------------
% 5.46/1.08  % (14425)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.46/1.09  % (14234)Time limit reached!
% 5.46/1.09  % (14234)------------------------------
% 5.46/1.09  % (14234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.46/1.09  % (14234)Termination reason: Time limit
% 5.46/1.09  
% 5.46/1.09  % (14234)Memory used [KB]: 13432
% 5.46/1.09  % (14234)Time elapsed: 0.636 s
% 5.46/1.09  % (14234)------------------------------
% 5.46/1.09  % (14234)------------------------------
% 5.46/1.09  % (14430)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.12/1.17  % (14447)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.12/1.18  % (14447)Refutation not found, incomplete strategy% (14447)------------------------------
% 6.12/1.18  % (14447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.12/1.18  % (14447)Termination reason: Refutation not found, incomplete strategy
% 6.12/1.18  
% 6.12/1.18  % (14447)Memory used [KB]: 1791
% 6.12/1.18  % (14447)Time elapsed: 0.104 s
% 6.12/1.18  % (14447)------------------------------
% 6.12/1.18  % (14447)------------------------------
% 6.12/1.19  % (14459)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.45/1.20  % (14454)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.45/1.23  % (14248)Time limit reached!
% 6.45/1.23  % (14248)------------------------------
% 6.45/1.23  % (14248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.45/1.23  % (14248)Termination reason: Time limit
% 6.45/1.23  
% 6.45/1.23  % (14248)Memory used [KB]: 3070
% 6.45/1.23  % (14248)Time elapsed: 0.806 s
% 6.45/1.23  % (14248)------------------------------
% 6.45/1.23  % (14248)------------------------------
% 6.82/1.25  % (14254)Refutation found. Thanks to Tanya!
% 6.82/1.25  % SZS status Theorem for theBenchmark
% 6.82/1.25  % SZS output start Proof for theBenchmark
% 6.82/1.25  fof(f6149,plain,(
% 6.82/1.25    $false),
% 6.82/1.25    inference(avatar_sat_refutation,[],[f123,f124,f125,f2550,f2557,f4210,f5734,f5735,f5767,f5819,f6148])).
% 6.82/1.25  fof(f6148,plain,(
% 6.82/1.25    spl10_3 | ~spl10_11 | spl10_16),
% 6.82/1.25    inference(avatar_contradiction_clause,[],[f6147])).
% 6.82/1.25  fof(f6147,plain,(
% 6.82/1.25    $false | (spl10_3 | ~spl10_11 | spl10_16)),
% 6.82/1.25    inference(subsumption_resolution,[],[f6146,f2539])).
% 6.82/1.25  fof(f2539,plain,(
% 6.82/1.25    r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | ~spl10_11),
% 6.82/1.25    inference(avatar_component_clause,[],[f2538])).
% 6.82/1.25  fof(f2538,plain,(
% 6.82/1.25    spl10_11 <=> r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 6.82/1.25    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 6.82/1.25  fof(f6146,plain,(
% 6.82/1.25    ~r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | (spl10_3 | spl10_16)),
% 6.82/1.25    inference(subsumption_resolution,[],[f6143,f121])).
% 6.82/1.25  fof(f121,plain,(
% 6.82/1.25    ~r2_hidden(sK6,sK7) | spl10_3),
% 6.82/1.25    inference(avatar_component_clause,[],[f120])).
% 6.82/1.25  fof(f120,plain,(
% 6.82/1.25    spl10_3 <=> r2_hidden(sK6,sK7)),
% 6.82/1.25    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 6.82/1.25  fof(f6143,plain,(
% 6.82/1.25    r2_hidden(sK6,sK7) | ~r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | spl10_16),
% 6.82/1.25    inference(resolution,[],[f6138,f77])).
% 6.82/1.25  fof(f77,plain,(
% 6.82/1.25    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 6.82/1.25    inference(cnf_transformation,[],[f45])).
% 6.82/1.25  fof(f45,plain,(
% 6.82/1.25    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2)))),
% 6.82/1.25    inference(rectify,[],[f44])).
% 6.82/1.25  fof(f44,plain,(
% 6.82/1.25    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP2(X2,X0,X1)))),
% 6.82/1.25    inference(nnf_transformation,[],[f27])).
% 6.82/1.26  fof(f27,plain,(
% 6.82/1.26    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 6.82/1.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 6.82/1.26  fof(f6138,plain,(
% 6.82/1.26    ~sP2(sK7,sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | spl10_16),
% 6.82/1.26    inference(resolution,[],[f4196,f148])).
% 6.82/1.26  fof(f148,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X1,X0)) | ~sP2(X1,X2,X0)) )),
% 6.82/1.26    inference(superposition,[],[f80,f59])).
% 6.82/1.26  fof(f59,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f2])).
% 6.82/1.26  fof(f2,axiom,(
% 6.82/1.26    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 6.82/1.26  fof(f80,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f46])).
% 6.82/1.26  fof(f46,plain,(
% 6.82/1.26    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 6.82/1.26    inference(nnf_transformation,[],[f28])).
% 6.82/1.26  fof(f28,plain,(
% 6.82/1.26    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP2(X2,X0,X1))),
% 6.82/1.26    inference(definition_folding,[],[f22,f27])).
% 6.82/1.26  fof(f22,plain,(
% 6.82/1.26    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 6.82/1.26    inference(ennf_transformation,[],[f5])).
% 6.82/1.26  fof(f5,axiom,(
% 6.82/1.26    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 6.82/1.26  fof(f4196,plain,(
% 6.82/1.26    ~r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_16),
% 6.82/1.26    inference(avatar_component_clause,[],[f4194])).
% 6.82/1.26  fof(f4194,plain,(
% 6.82/1.26    spl10_16 <=> r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))),
% 6.82/1.26    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 6.82/1.26  fof(f5819,plain,(
% 6.82/1.26    ~spl10_12 | spl10_1),
% 6.82/1.26    inference(avatar_split_clause,[],[f5818,f112,f2542])).
% 6.82/1.26  fof(f2542,plain,(
% 6.82/1.26    spl10_12 <=> k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))),
% 6.82/1.26    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 6.82/1.26  fof(f112,plain,(
% 6.82/1.26    spl10_1 <=> k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 6.82/1.26    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 6.82/1.26  fof(f5818,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_1),
% 6.82/1.26    inference(forward_demodulation,[],[f5811,f59])).
% 6.82/1.26  fof(f5811,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) | spl10_1),
% 6.82/1.26    inference(superposition,[],[f216,f253])).
% 6.82/1.26  fof(f253,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 6.82/1.26    inference(forward_demodulation,[],[f235,f60])).
% 6.82/1.26  fof(f60,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f1])).
% 6.82/1.26  fof(f1,axiom,(
% 6.82/1.26    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.82/1.26  fof(f235,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 6.82/1.26    inference(superposition,[],[f64,f58])).
% 6.82/1.26  fof(f58,plain,(
% 6.82/1.26    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.82/1.26    inference(cnf_transformation,[],[f18])).
% 6.82/1.26  fof(f18,plain,(
% 6.82/1.26    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.82/1.26    inference(rectify,[],[f4])).
% 6.82/1.26  fof(f4,axiom,(
% 6.82/1.26    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 6.82/1.26  fof(f64,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f7])).
% 6.82/1.26  fof(f7,axiom,(
% 6.82/1.26    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 6.82/1.26  fof(f216,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_1),
% 6.82/1.26    inference(forward_demodulation,[],[f114,f60])).
% 6.82/1.26  fof(f114,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) | spl10_1),
% 6.82/1.26    inference(avatar_component_clause,[],[f112])).
% 6.82/1.26  fof(f5767,plain,(
% 6.82/1.26    ~spl10_15 | ~spl10_16 | spl10_12),
% 6.82/1.26    inference(avatar_split_clause,[],[f4188,f2542,f4194,f4190])).
% 6.82/1.26  fof(f4190,plain,(
% 6.82/1.26    spl10_15 <=> r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))),
% 6.82/1.26    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 6.82/1.26  fof(f4188,plain,(
% 6.82/1.26    ~r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | ~r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_12),
% 6.82/1.26    inference(trivial_inequality_removal,[],[f4185])).
% 6.82/1.26  fof(f4185,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) | ~r2_hidden(sK6,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | ~r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_12),
% 6.82/1.26    inference(superposition,[],[f2544,f103])).
% 6.82/1.26  fof(f103,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f65,f99,f99])).
% 6.82/1.26  fof(f99,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f61,f98])).
% 6.82/1.26  fof(f98,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f63,f97])).
% 6.82/1.26  fof(f97,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f81,f96])).
% 6.82/1.26  fof(f96,plain,(
% 6.82/1.26    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f92,f95])).
% 6.82/1.26  fof(f95,plain,(
% 6.82/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f93,f94])).
% 6.82/1.26  fof(f94,plain,(
% 6.82/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f14])).
% 6.82/1.26  fof(f14,axiom,(
% 6.82/1.26    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 6.82/1.26  fof(f93,plain,(
% 6.82/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f13])).
% 6.82/1.26  fof(f13,axiom,(
% 6.82/1.26    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 6.82/1.26  fof(f92,plain,(
% 6.82/1.26    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f12])).
% 6.82/1.26  fof(f12,axiom,(
% 6.82/1.26    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 6.82/1.26  fof(f81,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f11])).
% 6.82/1.26  fof(f11,axiom,(
% 6.82/1.26    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 6.82/1.26  fof(f63,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f10])).
% 6.82/1.26  fof(f10,axiom,(
% 6.82/1.26    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 6.82/1.26  fof(f61,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f9])).
% 6.82/1.26  fof(f9,axiom,(
% 6.82/1.26    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.82/1.26  fof(f65,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f21])).
% 6.82/1.26  fof(f21,plain,(
% 6.82/1.26    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 6.82/1.26    inference(flattening,[],[f20])).
% 6.82/1.26  fof(f20,plain,(
% 6.82/1.26    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 6.82/1.26    inference(ennf_transformation,[],[f15])).
% 6.82/1.26  fof(f15,axiom,(
% 6.82/1.26    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 6.82/1.26  fof(f2544,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_12),
% 6.82/1.26    inference(avatar_component_clause,[],[f2542])).
% 6.82/1.26  fof(f5735,plain,(
% 6.82/1.26    ~spl10_3 | ~spl10_1 | ~spl10_11),
% 6.82/1.26    inference(avatar_split_clause,[],[f5725,f2538,f112,f120])).
% 6.82/1.26  fof(f5725,plain,(
% 6.82/1.26    ~r2_hidden(sK6,sK7) | (~spl10_1 | ~spl10_11)),
% 6.82/1.26    inference(resolution,[],[f4779,f2539])).
% 6.82/1.26  fof(f4779,plain,(
% 6.82/1.26    ( ! [X1] : (~r2_hidden(X1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | ~r2_hidden(X1,sK7)) ) | ~spl10_1),
% 6.82/1.26    inference(resolution,[],[f4676,f72])).
% 6.82/1.26  fof(f72,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f42])).
% 6.82/1.26  fof(f42,plain,(
% 6.82/1.26    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 6.82/1.26    inference(rectify,[],[f41])).
% 6.82/1.26  fof(f41,plain,(
% 6.82/1.26    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 6.82/1.26    inference(flattening,[],[f40])).
% 6.82/1.26  fof(f40,plain,(
% 6.82/1.26    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 6.82/1.26    inference(nnf_transformation,[],[f24])).
% 6.82/1.26  fof(f24,plain,(
% 6.82/1.26    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 6.82/1.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.82/1.26  fof(f4676,plain,(
% 6.82/1.26    ( ! [X0] : (~sP0(sK7,X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ) | ~spl10_1),
% 6.82/1.26    inference(resolution,[],[f4675,f187])).
% 6.82/1.26  fof(f187,plain,(
% 6.82/1.26    ( ! [X4,X5,X3] : (r2_hidden(X4,k3_xboole_0(X3,X5)) | ~sP0(X3,X4,X5)) )),
% 6.82/1.26    inference(resolution,[],[f67,f127])).
% 6.82/1.26  fof(f127,plain,(
% 6.82/1.26    ( ! [X2,X1] : (sP1(X1,X2,k3_xboole_0(X2,X1))) )),
% 6.82/1.26    inference(superposition,[],[f106,f60])).
% 6.82/1.26  fof(f106,plain,(
% 6.82/1.26    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 6.82/1.26    inference(equality_resolution,[],[f73])).
% 6.82/1.26  fof(f73,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 6.82/1.26    inference(cnf_transformation,[],[f43])).
% 6.82/1.26  fof(f43,plain,(
% 6.82/1.26    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 6.82/1.26    inference(nnf_transformation,[],[f26])).
% 6.82/1.26  fof(f26,plain,(
% 6.82/1.26    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 6.82/1.26    inference(definition_folding,[],[f3,f25,f24])).
% 6.82/1.26  fof(f25,plain,(
% 6.82/1.26    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 6.82/1.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.82/1.26  fof(f3,axiom,(
% 6.82/1.26    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 6.82/1.26  fof(f67,plain,(
% 6.82/1.26    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f39])).
% 6.82/1.26  fof(f39,plain,(
% 6.82/1.26    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 6.82/1.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).
% 6.82/1.26  fof(f38,plain,(
% 6.82/1.26    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 6.82/1.26    introduced(choice_axiom,[])).
% 6.82/1.26  fof(f37,plain,(
% 6.82/1.26    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 6.82/1.26    inference(rectify,[],[f36])).
% 6.82/1.26  fof(f36,plain,(
% 6.82/1.26    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 6.82/1.26    inference(nnf_transformation,[],[f25])).
% 6.82/1.26  fof(f4675,plain,(
% 6.82/1.26    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))) ) | ~spl10_1),
% 6.82/1.26    inference(resolution,[],[f4674,f110])).
% 6.82/1.26  fof(f110,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 6.82/1.26    inference(equality_resolution,[],[f105])).
% 6.82/1.26  fof(f105,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 6.82/1.26    inference(definition_unfolding,[],[f90,f98])).
% 6.82/1.26  fof(f90,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 6.82/1.26    inference(cnf_transformation,[],[f54])).
% 6.82/1.26  fof(f54,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) & (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 6.82/1.26    inference(nnf_transformation,[],[f31])).
% 6.82/1.26  fof(f31,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP4(X0,X1,X2,X3))),
% 6.82/1.26    inference(definition_folding,[],[f23,f30,f29])).
% 6.82/1.26  fof(f29,plain,(
% 6.82/1.26    ! [X4,X2,X1,X0] : (sP3(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 6.82/1.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 6.82/1.26  fof(f30,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : (sP4(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP3(X4,X2,X1,X0)))),
% 6.82/1.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 6.82/1.26  fof(f23,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 6.82/1.26    inference(ennf_transformation,[],[f8])).
% 6.82/1.26  fof(f8,axiom,(
% 6.82/1.26    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 6.82/1.26  fof(f4674,plain,(
% 6.82/1.26    ( ! [X4,X3] : (~sP4(sK5,sK5,sK6,X4) | ~r2_hidden(X3,k3_xboole_0(sK7,X4))) ) | ~spl10_1),
% 6.82/1.26    inference(subsumption_resolution,[],[f4672,f4655])).
% 6.82/1.26  fof(f4655,plain,(
% 6.82/1.26    ( ! [X2,X1] : (~sP4(sK5,sK5,sK6,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k3_xboole_0(sK7,X2))) ) | ~spl10_1),
% 6.82/1.26    inference(duplicate_literal_removal,[],[f4644])).
% 6.82/1.26  fof(f4644,plain,(
% 6.82/1.26    ( ! [X2,X1] : (~r2_hidden(X1,X2) | ~sP4(sK5,sK5,sK6,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k3_xboole_0(sK7,X2))) ) | ~spl10_1),
% 6.82/1.26    inference(resolution,[],[f4583,f76])).
% 6.82/1.26  fof(f76,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f45])).
% 6.82/1.26  fof(f4583,plain,(
% 6.82/1.26    ( ! [X0,X1] : (sP2(k3_xboole_0(sK7,X0),X1,X0) | ~r2_hidden(X1,X0) | ~sP4(sK5,sK5,sK6,X0)) ) | ~spl10_1),
% 6.82/1.26    inference(superposition,[],[f4241,f104])).
% 6.82/1.26  fof(f104,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 6.82/1.26    inference(definition_unfolding,[],[f91,f98])).
% 6.82/1.26  fof(f91,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f54])).
% 6.82/1.26  fof(f4241,plain,(
% 6.82/1.26    ( ! [X1] : (sP2(k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),X1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | ~r2_hidden(X1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ) | ~spl10_1),
% 6.82/1.26    inference(superposition,[],[f79,f4211])).
% 6.82/1.26  fof(f4211,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | ~spl10_1),
% 6.82/1.26    inference(forward_demodulation,[],[f113,f60])).
% 6.82/1.26  fof(f113,plain,(
% 6.82/1.26    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) | ~spl10_1),
% 6.82/1.26    inference(avatar_component_clause,[],[f112])).
% 6.82/1.26  fof(f79,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f46])).
% 6.82/1.26  fof(f4672,plain,(
% 6.82/1.26    ( ! [X4,X3] : (r2_hidden(X3,X4) | ~sP4(sK5,sK5,sK6,X4) | ~r2_hidden(X3,k3_xboole_0(sK7,X4))) ) | ~spl10_1),
% 6.82/1.26    inference(duplicate_literal_removal,[],[f4660])).
% 6.82/1.26  fof(f4660,plain,(
% 6.82/1.26    ( ! [X4,X3] : (r2_hidden(X3,X4) | ~sP4(sK5,sK5,sK6,X4) | r2_hidden(X3,X4) | ~r2_hidden(X3,k3_xboole_0(sK7,X4))) ) | ~spl10_1),
% 6.82/1.26    inference(resolution,[],[f4640,f78])).
% 6.82/1.26  fof(f78,plain,(
% 6.82/1.26    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f45])).
% 6.82/1.26  fof(f4640,plain,(
% 6.82/1.26    ( ! [X0,X1] : (~sP2(k3_xboole_0(sK7,X0),X1,X0) | r2_hidden(X1,X0) | ~sP4(sK5,sK5,sK6,X0)) ) | ~spl10_1),
% 6.82/1.26    inference(superposition,[],[f4242,f104])).
% 6.82/1.26  fof(f4242,plain,(
% 6.82/1.26    ( ! [X2] : (~sP2(k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),X2,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | r2_hidden(X2,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ) | ~spl10_1),
% 6.82/1.26    inference(superposition,[],[f80,f4211])).
% 6.82/1.26  fof(f5734,plain,(
% 6.82/1.26    ~spl10_2 | ~spl10_1 | ~spl10_10),
% 6.82/1.26    inference(avatar_split_clause,[],[f5724,f2534,f112,f116])).
% 6.82/1.26  fof(f116,plain,(
% 6.82/1.26    spl10_2 <=> r2_hidden(sK5,sK7)),
% 6.82/1.26    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 6.82/1.26  fof(f2534,plain,(
% 6.82/1.26    spl10_10 <=> r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 6.82/1.26    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 6.82/1.26  fof(f5724,plain,(
% 6.82/1.26    ~r2_hidden(sK5,sK7) | (~spl10_1 | ~spl10_10)),
% 6.82/1.26    inference(resolution,[],[f4779,f2535])).
% 6.82/1.26  fof(f2535,plain,(
% 6.82/1.26    r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | ~spl10_10),
% 6.82/1.26    inference(avatar_component_clause,[],[f2534])).
% 6.82/1.26  fof(f4210,plain,(
% 6.82/1.26    spl10_2 | ~spl10_10 | spl10_15),
% 6.82/1.26    inference(avatar_split_clause,[],[f4209,f4190,f2534,f116])).
% 6.82/1.26  fof(f4209,plain,(
% 6.82/1.26    r2_hidden(sK5,sK7) | (~spl10_10 | spl10_15)),
% 6.82/1.26    inference(subsumption_resolution,[],[f4203,f2535])).
% 6.82/1.26  fof(f4203,plain,(
% 6.82/1.26    r2_hidden(sK5,sK7) | ~r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | spl10_15),
% 6.82/1.26    inference(resolution,[],[f4198,f77])).
% 6.82/1.26  fof(f4198,plain,(
% 6.82/1.26    ~sP2(sK7,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | spl10_15),
% 6.82/1.26    inference(resolution,[],[f4192,f148])).
% 6.82/1.26  fof(f4192,plain,(
% 6.82/1.26    ~r2_hidden(sK5,k5_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) | spl10_15),
% 6.82/1.26    inference(avatar_component_clause,[],[f4190])).
% 6.82/1.26  fof(f2557,plain,(
% 6.82/1.26    spl10_11),
% 6.82/1.26    inference(avatar_contradiction_clause,[],[f2556])).
% 6.82/1.26  fof(f2556,plain,(
% 6.82/1.26    $false | spl10_11),
% 6.82/1.26    inference(subsumption_resolution,[],[f2554,f107])).
% 6.82/1.26  fof(f107,plain,(
% 6.82/1.26    ( ! [X2,X3,X1] : (sP3(X1,X1,X2,X3)) )),
% 6.82/1.26    inference(equality_resolution,[],[f89])).
% 6.82/1.26  fof(f89,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X1) )),
% 6.82/1.26    inference(cnf_transformation,[],[f53])).
% 6.82/1.26  fof(f53,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP3(X0,X1,X2,X3)))),
% 6.82/1.26    inference(rectify,[],[f52])).
% 6.82/1.26  fof(f52,plain,(
% 6.82/1.26    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP3(X4,X2,X1,X0)))),
% 6.82/1.26    inference(flattening,[],[f51])).
% 6.82/1.26  fof(f51,plain,(
% 6.82/1.26    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP3(X4,X2,X1,X0)))),
% 6.82/1.26    inference(nnf_transformation,[],[f29])).
% 6.82/1.26  fof(f2554,plain,(
% 6.82/1.26    ~sP3(sK6,sK6,sK5,sK5) | spl10_11),
% 6.82/1.26    inference(resolution,[],[f2540,f404])).
% 6.82/1.26  fof(f404,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP3(X0,X1,X2,X3)) )),
% 6.82/1.26    inference(resolution,[],[f110,f83])).
% 6.82/1.26  fof(f83,plain,(
% 6.82/1.26    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 6.82/1.26    inference(cnf_transformation,[],[f50])).
% 6.82/1.26  fof(f50,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 6.82/1.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 6.82/1.26  fof(f49,plain,(
% 6.82/1.26    ! [X3,X2,X1,X0] : (? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3))))),
% 6.82/1.26    introduced(choice_axiom,[])).
% 6.82/1.26  fof(f48,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 6.82/1.26    inference(rectify,[],[f47])).
% 6.82/1.26  fof(f47,plain,(
% 6.82/1.26    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP3(X4,X2,X1,X0)) & (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP4(X0,X1,X2,X3)))),
% 6.82/1.26    inference(nnf_transformation,[],[f30])).
% 6.82/1.26  fof(f2540,plain,(
% 6.82/1.26    ~r2_hidden(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | spl10_11),
% 6.82/1.26    inference(avatar_component_clause,[],[f2538])).
% 6.82/1.26  fof(f2550,plain,(
% 6.82/1.26    spl10_10),
% 6.82/1.26    inference(avatar_contradiction_clause,[],[f2549])).
% 6.82/1.26  fof(f2549,plain,(
% 6.82/1.26    $false | spl10_10),
% 6.82/1.26    inference(subsumption_resolution,[],[f2547,f108])).
% 6.82/1.26  fof(f108,plain,(
% 6.82/1.26    ( ! [X2,X3,X1] : (sP3(X2,X1,X2,X3)) )),
% 6.82/1.26    inference(equality_resolution,[],[f88])).
% 6.82/1.26  fof(f88,plain,(
% 6.82/1.26    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X2) )),
% 6.82/1.26    inference(cnf_transformation,[],[f53])).
% 6.82/1.26  fof(f2547,plain,(
% 6.82/1.26    ~sP3(sK5,sK6,sK5,sK5) | spl10_10),
% 6.82/1.26    inference(resolution,[],[f2536,f404])).
% 6.82/1.26  fof(f2536,plain,(
% 6.82/1.26    ~r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) | spl10_10),
% 6.82/1.26    inference(avatar_component_clause,[],[f2534])).
% 6.82/1.26  fof(f125,plain,(
% 6.82/1.26    spl10_1 | ~spl10_2),
% 6.82/1.26    inference(avatar_split_clause,[],[f102,f116,f112])).
% 6.82/1.26  fof(f102,plain,(
% 6.82/1.26    ~r2_hidden(sK5,sK7) | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 6.82/1.26    inference(definition_unfolding,[],[f55,f99,f62,f99])).
% 6.82/1.26  fof(f62,plain,(
% 6.82/1.26    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.82/1.26    inference(cnf_transformation,[],[f6])).
% 6.82/1.26  fof(f6,axiom,(
% 6.82/1.26    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.82/1.26  fof(f55,plain,(
% 6.82/1.26    ~r2_hidden(sK5,sK7) | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 6.82/1.26    inference(cnf_transformation,[],[f35])).
% 6.82/1.26  fof(f35,plain,(
% 6.82/1.26    (r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k2_tarski(sK5,sK6) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)) & ((~r2_hidden(sK6,sK7) & ~r2_hidden(sK5,sK7)) | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 6.82/1.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f34])).
% 6.82/1.26  fof(f34,plain,(
% 6.82/1.26    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k2_tarski(sK5,sK6) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)) & ((~r2_hidden(sK6,sK7) & ~r2_hidden(sK5,sK7)) | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 6.82/1.26    introduced(choice_axiom,[])).
% 6.82/1.26  fof(f33,plain,(
% 6.82/1.26    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 6.82/1.26    inference(flattening,[],[f32])).
% 6.82/1.26  fof(f32,plain,(
% 6.82/1.26    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 6.82/1.26    inference(nnf_transformation,[],[f19])).
% 6.82/1.26  fof(f19,plain,(
% 6.82/1.26    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 6.82/1.26    inference(ennf_transformation,[],[f17])).
% 6.82/1.26  fof(f17,negated_conjecture,(
% 6.82/1.26    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 6.82/1.26    inference(negated_conjecture,[],[f16])).
% 6.82/1.26  fof(f16,conjecture,(
% 6.82/1.26    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 6.82/1.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 6.82/1.26  fof(f124,plain,(
% 6.82/1.26    spl10_1 | ~spl10_3),
% 6.82/1.26    inference(avatar_split_clause,[],[f101,f120,f112])).
% 6.82/1.26  fof(f101,plain,(
% 6.82/1.26    ~r2_hidden(sK6,sK7) | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 6.82/1.26    inference(definition_unfolding,[],[f56,f99,f62,f99])).
% 6.82/1.26  fof(f56,plain,(
% 6.82/1.26    ~r2_hidden(sK6,sK7) | k2_tarski(sK5,sK6) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 6.82/1.26    inference(cnf_transformation,[],[f35])).
% 6.82/1.26  fof(f123,plain,(
% 6.82/1.26    ~spl10_1 | spl10_2 | spl10_3),
% 6.82/1.26    inference(avatar_split_clause,[],[f100,f120,f116,f112])).
% 6.82/1.26  fof(f100,plain,(
% 6.82/1.26    r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 6.82/1.26    inference(definition_unfolding,[],[f57,f99,f62,f99])).
% 6.82/1.26  fof(f57,plain,(
% 6.82/1.26    r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k2_tarski(sK5,sK6) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 6.82/1.26    inference(cnf_transformation,[],[f35])).
% 6.82/1.26  % SZS output end Proof for theBenchmark
% 6.82/1.26  % (14254)------------------------------
% 6.82/1.26  % (14254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.26  % (14254)Termination reason: Refutation
% 6.82/1.26  
% 6.82/1.26  % (14254)Memory used [KB]: 9850
% 6.82/1.26  % (14254)Time elapsed: 0.824 s
% 6.82/1.26  % (14254)------------------------------
% 6.82/1.26  % (14254)------------------------------
% 6.82/1.26  % (14225)Success in time 0.884 s
%------------------------------------------------------------------------------
