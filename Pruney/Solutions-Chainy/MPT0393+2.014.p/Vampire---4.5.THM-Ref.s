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
% DateTime   : Thu Dec  3 12:45:53 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 169 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  201 ( 346 expanded)
%              Number of equality atoms :   84 ( 170 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2819,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f132,f2657,f2667,f2737,f2786,f2797,f2818])).

fof(f2818,plain,(
    spl7_45 ),
    inference(avatar_contradiction_clause,[],[f2817])).

fof(f2817,plain,
    ( $false
    | spl7_45 ),
    inference(resolution,[],[f2796,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2796,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f2794])).

fof(f2794,plain,
    ( spl7_45
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f2797,plain,
    ( spl7_3
    | spl7_25
    | ~ spl7_45
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f2791,f2520,f2794,f2516,f120])).

fof(f120,plain,
    ( spl7_3
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f2516,plain,
    ( spl7_25
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f2520,plain,
    ( spl7_26
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f2791,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl7_26 ),
    inference(superposition,[],[f35,f2522])).

fof(f2522,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f2520])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f2786,plain,
    ( spl7_25
    | spl7_26
    | spl7_3 ),
    inference(avatar_split_clause,[],[f2785,f120,f2520,f2516])).

fof(f2785,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl7_3 ),
    inference(duplicate_literal_removal,[],[f2784])).

fof(f2784,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl7_3 ),
    inference(resolution,[],[f122,f289])).

fof(f289,plain,(
    ! [X14,X15,X13,X16] :
      ( r1_tarski(X16,k1_setfam_1(k2_enumset1(X14,X14,X13,X15)))
      | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X15
      | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X14
      | k1_xboole_0 = k2_enumset1(X14,X14,X13,X15)
      | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X13 ) ),
    inference(resolution,[],[f97,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f122,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f2737,plain,
    ( ~ spl7_3
    | ~ spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f2731,f99,f116,f120])).

fof(f116,plain,
    ( spl7_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f99,plain,
    ( spl7_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2731,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl7_1 ),
    inference(extensionality_resolution,[],[f38,f101])).

fof(f101,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2667,plain,
    ( spl7_31
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f2559,f2516,f2654])).

fof(f2654,plain,
    ( spl7_31
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f2559,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_25 ),
    inference(superposition,[],[f1382,f2518])).

fof(f2518,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f1382,plain,(
    ! [X26] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(X26,X26,X26,X26)) ),
    inference(resolution,[],[f1373,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f134,f38])).

fof(f134,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f104,f105])).

fof(f105,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,k1_xboole_0,X1)) ),
    inference(resolution,[],[f94,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f94,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f52])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,(
    ! [X4,X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X3,X4)),X4) ),
    inference(resolution,[],[f92,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f92,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f64,f52])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1373,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) ),
    inference(duplicate_literal_removal,[],[f1355])).

fof(f1355,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0)
      | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) ) ),
    inference(resolution,[],[f185,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2),X0)
      | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2) ) ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f2657,plain,
    ( ~ spl7_31
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f2537,f2516,f2654])).

fof(f2537,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_25 ),
    inference(superposition,[],[f89,f2518])).

fof(f89,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f51,f66,f66,f66])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f132,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f104,f118])).

fof(f118,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f102,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f67,f99])).

fof(f67,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f28,f66])).

fof(f28,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:48:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (2118)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (2126)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (2126)Refutation not found, incomplete strategy% (2126)------------------------------
% 0.22/0.54  % (2126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2126)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2126)Memory used [KB]: 10618
% 0.22/0.54  % (2126)Time elapsed: 0.114 s
% 0.22/0.54  % (2126)------------------------------
% 0.22/0.54  % (2126)------------------------------
% 0.22/0.54  % (2141)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (2133)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (2118)Refutation not found, incomplete strategy% (2118)------------------------------
% 0.22/0.54  % (2118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2118)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2118)Memory used [KB]: 1663
% 0.22/0.54  % (2118)Time elapsed: 0.123 s
% 0.22/0.54  % (2118)------------------------------
% 0.22/0.54  % (2118)------------------------------
% 0.22/0.55  % (2134)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.56  % (2125)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.56  % (2123)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.56  % (2121)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.57  % (2122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.58  % (2142)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.64/0.58  % (2139)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.58  % (2130)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.58  % (2124)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.58  % (2120)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.58  % (2119)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.58  % (2120)Refutation not found, incomplete strategy% (2120)------------------------------
% 1.64/0.58  % (2120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (2120)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (2120)Memory used [KB]: 10746
% 1.64/0.58  % (2120)Time elapsed: 0.151 s
% 1.64/0.58  % (2120)------------------------------
% 1.64/0.58  % (2120)------------------------------
% 1.64/0.59  % (2136)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.59  % (2146)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.64/0.59  % (2140)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.64/0.60  % (2147)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.60  % (2128)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.64/0.60  % (2135)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.64/0.60  % (2128)Refutation not found, incomplete strategy% (2128)------------------------------
% 1.64/0.60  % (2128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (2145)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.64/0.60  % (2128)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (2128)Memory used [KB]: 10618
% 1.64/0.60  % (2128)Time elapsed: 0.175 s
% 1.64/0.60  % (2128)------------------------------
% 1.64/0.60  % (2128)------------------------------
% 1.64/0.60  % (2139)Refutation not found, incomplete strategy% (2139)------------------------------
% 1.64/0.60  % (2139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (2139)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (2139)Memory used [KB]: 1791
% 1.64/0.60  % (2139)Time elapsed: 0.179 s
% 1.64/0.60  % (2139)------------------------------
% 1.64/0.60  % (2139)------------------------------
% 1.64/0.60  % (2137)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.60  % (2127)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.64/0.60  % (2131)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.64/0.61  % (2138)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.64/0.61  % (2138)Refutation not found, incomplete strategy% (2138)------------------------------
% 1.64/0.61  % (2138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (2138)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (2138)Memory used [KB]: 10746
% 1.64/0.61  % (2138)Time elapsed: 0.180 s
% 1.64/0.61  % (2138)------------------------------
% 1.64/0.61  % (2138)------------------------------
% 1.64/0.61  % (2129)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.64/0.61  % (2129)Refutation not found, incomplete strategy% (2129)------------------------------
% 1.64/0.61  % (2129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (2129)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (2129)Memory used [KB]: 10618
% 1.64/0.61  % (2129)Time elapsed: 0.191 s
% 1.64/0.61  % (2129)------------------------------
% 1.64/0.61  % (2129)------------------------------
% 1.64/0.61  % (2132)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.62  % (2144)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.64/0.62  % (2143)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.32/0.69  % (2182)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.32/0.69  % (2183)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.32/0.70  % (2182)Refutation not found, incomplete strategy% (2182)------------------------------
% 2.32/0.70  % (2182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.70  % (2182)Termination reason: Refutation not found, incomplete strategy
% 2.32/0.70  
% 2.32/0.70  % (2182)Memory used [KB]: 6140
% 2.32/0.70  % (2182)Time elapsed: 0.069 s
% 2.32/0.70  % (2182)------------------------------
% 2.32/0.70  % (2182)------------------------------
% 2.66/0.74  % (2184)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.75/0.75  % (2134)Refutation found. Thanks to Tanya!
% 2.75/0.75  % SZS status Theorem for theBenchmark
% 2.75/0.75  % SZS output start Proof for theBenchmark
% 2.75/0.75  fof(f2819,plain,(
% 2.75/0.75    $false),
% 2.75/0.75    inference(avatar_sat_refutation,[],[f102,f132,f2657,f2667,f2737,f2786,f2797,f2818])).
% 2.75/0.75  fof(f2818,plain,(
% 2.75/0.75    spl7_45),
% 2.75/0.75    inference(avatar_contradiction_clause,[],[f2817])).
% 2.75/0.75  fof(f2817,plain,(
% 2.75/0.75    $false | spl7_45),
% 2.75/0.75    inference(resolution,[],[f2796,f84])).
% 2.75/0.75  fof(f84,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.75/0.75    inference(equality_resolution,[],[f37])).
% 2.75/0.75  fof(f37,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.75/0.75    inference(cnf_transformation,[],[f2])).
% 2.75/0.75  fof(f2,axiom,(
% 2.75/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.75/0.75  fof(f2796,plain,(
% 2.75/0.75    ~r1_tarski(sK0,sK0) | spl7_45),
% 2.75/0.75    inference(avatar_component_clause,[],[f2794])).
% 2.75/0.75  fof(f2794,plain,(
% 2.75/0.75    spl7_45 <=> r1_tarski(sK0,sK0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.75/0.75  fof(f2797,plain,(
% 2.75/0.75    spl7_3 | spl7_25 | ~spl7_45 | ~spl7_26),
% 2.75/0.75    inference(avatar_split_clause,[],[f2791,f2520,f2794,f2516,f120])).
% 2.75/0.75  fof(f120,plain,(
% 2.75/0.75    spl7_3 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.75/0.75  fof(f2516,plain,(
% 2.75/0.75    spl7_25 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.75/0.75  fof(f2520,plain,(
% 2.75/0.75    spl7_26 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.75/0.75  fof(f2791,plain,(
% 2.75/0.75    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl7_26),
% 2.75/0.75    inference(superposition,[],[f35,f2522])).
% 2.75/0.75  fof(f2522,plain,(
% 2.75/0.75    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl7_26),
% 2.75/0.75    inference(avatar_component_clause,[],[f2520])).
% 2.75/0.75  fof(f35,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f23])).
% 2.75/0.75  fof(f23,plain,(
% 2.75/0.75    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.75/0.75    inference(flattening,[],[f22])).
% 2.75/0.75  fof(f22,plain,(
% 2.75/0.75    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.75/0.75    inference(ennf_transformation,[],[f14])).
% 2.75/0.75  fof(f14,axiom,(
% 2.75/0.75    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.75/0.75  fof(f2786,plain,(
% 2.75/0.75    spl7_25 | spl7_26 | spl7_3),
% 2.75/0.75    inference(avatar_split_clause,[],[f2785,f120,f2520,f2516])).
% 2.75/0.75  fof(f2785,plain,(
% 2.75/0.75    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl7_3),
% 2.75/0.75    inference(duplicate_literal_removal,[],[f2784])).
% 2.75/0.75  fof(f2784,plain,(
% 2.75/0.75    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl7_3),
% 2.75/0.75    inference(resolution,[],[f122,f289])).
% 2.75/0.75  fof(f289,plain,(
% 2.75/0.75    ( ! [X14,X15,X13,X16] : (r1_tarski(X16,k1_setfam_1(k2_enumset1(X14,X14,X13,X15))) | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X15 | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X14 | k1_xboole_0 = k2_enumset1(X14,X14,X13,X15) | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X13) )),
% 2.75/0.75    inference(resolution,[],[f97,f34])).
% 2.75/0.75  fof(f34,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f23])).
% 2.75/0.75  fof(f97,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 2.75/0.75    inference(equality_resolution,[],[f79])).
% 2.75/0.75  fof(f79,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.75/0.75    inference(definition_unfolding,[],[f61,f52])).
% 2.75/0.75  fof(f52,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f6])).
% 2.75/0.75  fof(f6,axiom,(
% 2.75/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.75/0.75  fof(f61,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.75/0.75    inference(cnf_transformation,[],[f27])).
% 2.75/0.75  fof(f27,plain,(
% 2.75/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.75/0.75    inference(ennf_transformation,[],[f3])).
% 2.75/0.75  fof(f3,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.75/0.75  fof(f122,plain,(
% 2.75/0.75    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl7_3),
% 2.75/0.75    inference(avatar_component_clause,[],[f120])).
% 2.75/0.75  fof(f2737,plain,(
% 2.75/0.75    ~spl7_3 | ~spl7_2 | spl7_1),
% 2.75/0.75    inference(avatar_split_clause,[],[f2731,f99,f116,f120])).
% 2.75/0.75  fof(f116,plain,(
% 2.75/0.75    spl7_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.75/0.75  fof(f99,plain,(
% 2.75/0.75    spl7_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.75/0.75  fof(f2731,plain,(
% 2.75/0.75    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl7_1),
% 2.75/0.75    inference(extensionality_resolution,[],[f38,f101])).
% 2.75/0.75  fof(f101,plain,(
% 2.75/0.75    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl7_1),
% 2.75/0.75    inference(avatar_component_clause,[],[f99])).
% 2.75/0.75  fof(f38,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.75/0.75    inference(cnf_transformation,[],[f2])).
% 2.75/0.75  fof(f2667,plain,(
% 2.75/0.75    spl7_31 | ~spl7_25),
% 2.75/0.75    inference(avatar_split_clause,[],[f2559,f2516,f2654])).
% 2.75/0.75  fof(f2654,plain,(
% 2.75/0.75    spl7_31 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 2.75/0.75  fof(f2559,plain,(
% 2.75/0.75    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_25),
% 2.75/0.75    inference(superposition,[],[f1382,f2518])).
% 2.75/0.75  fof(f2518,plain,(
% 2.75/0.75    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl7_25),
% 2.75/0.75    inference(avatar_component_clause,[],[f2516])).
% 2.75/0.75  fof(f1382,plain,(
% 2.75/0.75    ( ! [X26] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(X26,X26,X26,X26))) )),
% 2.75/0.75    inference(resolution,[],[f1373,f136])).
% 2.75/0.75  fof(f136,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.75/0.75    inference(resolution,[],[f134,f38])).
% 2.75/0.75  fof(f134,plain,(
% 2.75/0.75    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.75/0.75    inference(superposition,[],[f104,f105])).
% 2.75/0.75  fof(f105,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,k1_xboole_0,X1))) )),
% 2.75/0.75    inference(resolution,[],[f94,f30])).
% 2.75/0.75  fof(f30,plain,(
% 2.75/0.75    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k1_setfam_1(X0)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f19])).
% 2.75/0.75  fof(f19,plain,(
% 2.75/0.75    ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | ~r2_hidden(k1_xboole_0,X0))),
% 2.75/0.75    inference(ennf_transformation,[],[f13])).
% 2.75/0.75  fof(f13,axiom,(
% 2.75/0.75    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).
% 2.75/0.75  fof(f94,plain,(
% 2.75/0.75    ( ! [X4,X2,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X4,X2))) )),
% 2.75/0.75    inference(equality_resolution,[],[f93])).
% 2.75/0.75  fof(f93,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X4,X2) != X3) )),
% 2.75/0.75    inference(equality_resolution,[],[f77])).
% 2.75/0.75  fof(f77,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.75/0.75    inference(definition_unfolding,[],[f63,f52])).
% 2.75/0.75  fof(f63,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.75/0.75    inference(cnf_transformation,[],[f27])).
% 2.75/0.75  fof(f104,plain,(
% 2.75/0.75    ( ! [X4,X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X3,X4)),X4)) )),
% 2.75/0.75    inference(resolution,[],[f92,f32])).
% 2.75/0.75  fof(f32,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f20])).
% 2.75/0.75  fof(f20,plain,(
% 2.75/0.75    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 2.75/0.75    inference(ennf_transformation,[],[f12])).
% 2.75/0.75  fof(f12,axiom,(
% 2.75/0.75    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 2.75/0.75  fof(f92,plain,(
% 2.75/0.75    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 2.75/0.75    inference(equality_resolution,[],[f91])).
% 2.75/0.75  fof(f91,plain,(
% 2.75/0.75    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 2.75/0.75    inference(equality_resolution,[],[f76])).
% 2.75/0.75  fof(f76,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.75/0.75    inference(definition_unfolding,[],[f64,f52])).
% 2.75/0.75  fof(f64,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.75/0.75    inference(cnf_transformation,[],[f27])).
% 2.75/0.75  fof(f1373,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0)) )),
% 2.75/0.75    inference(duplicate_literal_removal,[],[f1355])).
% 2.75/0.75  fof(f1355,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0)) )),
% 2.75/0.75    inference(resolution,[],[f185,f41])).
% 2.75/0.75  fof(f41,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f24])).
% 2.75/0.75  fof(f24,plain,(
% 2.75/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.75/0.75    inference(ennf_transformation,[],[f1])).
% 2.75/0.75  fof(f1,axiom,(
% 2.75/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.75/0.75  fof(f185,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2),X0) | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2)) )),
% 2.75/0.75    inference(resolution,[],[f75,f40])).
% 2.75/0.75  fof(f40,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f24])).
% 2.75/0.75  fof(f75,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | r2_hidden(X0,X1)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f54,f66])).
% 2.75/0.75  fof(f66,plain,(
% 2.75/0.75    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f29,f65])).
% 2.75/0.75  fof(f65,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f31,f52])).
% 2.75/0.75  fof(f31,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f5])).
% 2.75/0.75  fof(f5,axiom,(
% 2.75/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.75/0.75  fof(f29,plain,(
% 2.75/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f4])).
% 2.75/0.75  fof(f4,axiom,(
% 2.75/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.75/0.75  fof(f54,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f10])).
% 2.75/0.75  fof(f10,axiom,(
% 2.75/0.75    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.75/0.75  fof(f2657,plain,(
% 2.75/0.75    ~spl7_31 | ~spl7_25),
% 2.75/0.75    inference(avatar_split_clause,[],[f2537,f2516,f2654])).
% 2.75/0.75  fof(f2537,plain,(
% 2.75/0.75    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_25),
% 2.75/0.75    inference(superposition,[],[f89,f2518])).
% 2.75/0.75  fof(f89,plain,(
% 2.75/0.75    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 2.75/0.75    inference(equality_resolution,[],[f71])).
% 2.75/0.75  fof(f71,plain,(
% 2.75/0.75    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 2.75/0.75    inference(definition_unfolding,[],[f51,f66,f66,f66])).
% 2.75/0.75  fof(f51,plain,(
% 2.75/0.75    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f9])).
% 2.75/0.75  fof(f9,axiom,(
% 2.75/0.75    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.75/0.75  fof(f132,plain,(
% 2.75/0.75    spl7_2),
% 2.75/0.75    inference(avatar_contradiction_clause,[],[f129])).
% 2.75/0.75  fof(f129,plain,(
% 2.75/0.75    $false | spl7_2),
% 2.75/0.75    inference(resolution,[],[f104,f118])).
% 2.75/0.75  fof(f118,plain,(
% 2.75/0.75    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl7_2),
% 2.75/0.75    inference(avatar_component_clause,[],[f116])).
% 2.75/0.75  fof(f102,plain,(
% 2.75/0.75    ~spl7_1),
% 2.75/0.75    inference(avatar_split_clause,[],[f67,f99])).
% 2.75/0.75  fof(f67,plain,(
% 2.75/0.75    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.75/0.75    inference(definition_unfolding,[],[f28,f66])).
% 2.75/0.75  fof(f28,plain,(
% 2.75/0.75    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.75/0.75    inference(cnf_transformation,[],[f18])).
% 2.75/0.75  fof(f18,plain,(
% 2.75/0.75    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.75/0.75    inference(ennf_transformation,[],[f17])).
% 2.75/0.75  fof(f17,negated_conjecture,(
% 2.75/0.75    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.75/0.75    inference(negated_conjecture,[],[f16])).
% 2.75/0.75  fof(f16,conjecture,(
% 2.75/0.75    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.75/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.75/0.75  % SZS output end Proof for theBenchmark
% 2.75/0.75  % (2134)------------------------------
% 2.75/0.75  % (2134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.75  % (2134)Termination reason: Refutation
% 2.75/0.75  
% 2.75/0.75  % (2134)Memory used [KB]: 14456
% 2.75/0.75  % (2134)Time elapsed: 0.325 s
% 2.75/0.75  % (2134)------------------------------
% 2.75/0.75  % (2134)------------------------------
% 2.75/0.76  % (2117)Success in time 0.386 s
%------------------------------------------------------------------------------
