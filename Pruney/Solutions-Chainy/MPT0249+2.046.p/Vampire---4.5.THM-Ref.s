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
% DateTime   : Thu Dec  3 12:38:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 229 expanded)
%              Number of leaves         :   26 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 ( 416 expanded)
%              Number of equality atoms :   83 ( 238 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f100,f112,f117,f146,f226,f233,f237,f238])).

fof(f238,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f237,plain,
    ( spl7_6
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl7_6
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f107,f232,f185])).

fof(f185,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK1,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl7_8 ),
    inference(superposition,[],[f32,f163])).

fof(f163,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f128,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f128,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | sK0 = X4 )
    | ~ spl7_8 ),
    inference(superposition,[],[f64,f116])).

fof(f116,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_8
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f232,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl7_19
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_6
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f233,plain,
    ( spl7_3
    | spl7_19
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f228,f223,f230,f83])).

fof(f83,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f223,plain,
    ( spl7_18
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f228,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_18 ),
    inference(superposition,[],[f25,f225])).

fof(f225,plain,
    ( sK0 = sK3(sK2)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f223])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f226,plain,
    ( spl7_3
    | spl7_18
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f206,f143,f114,f223,f83])).

fof(f143,plain,
    ( spl7_11
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f206,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f204,f25])).

fof(f204,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | sK0 = X1 )
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f202,f128])).

fof(f202,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_11 ),
    inference(condensation,[],[f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_11 ),
    inference(resolution,[],[f193,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f193,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(X2,sK1))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl7_11 ),
    inference(superposition,[],[f70,f158])).

fof(f158,plain,
    ( ! [X0] : k4_xboole_0(X0,sK1) = k4_xboole_0(k4_xboole_0(X0,sK1),sK2)
    | ~ spl7_11 ),
    inference(superposition,[],[f63,f145])).

fof(f145,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f146,plain,
    ( spl7_11
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f119,f114,f88,f143])).

fof(f88,plain,
    ( spl7_4
  <=> k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f119,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f90,f116])).

fof(f90,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f117,plain,
    ( spl7_2
    | spl7_8
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f101,f97,f114,f78])).

fof(f78,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f97,plain,
    ( spl7_5
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f101,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ spl7_5 ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f52,f52])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f99,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f112,plain,
    ( ~ spl7_6
    | spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f92,f88,f109,f105])).

fof(f109,plain,
    ( spl7_7
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f92,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl7_4 ),
    inference(superposition,[],[f90,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f51])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f100,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f95,f88,f97])).

fof(f95,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl7_4 ),
    inference(superposition,[],[f54,f90])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f91,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f53,f88])).

fof(f53,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f51,f52])).

fof(f20,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f86,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f23,f83])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f22,f78])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f21,f73])).

fof(f73,plain,
    ( spl7_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (2123)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (2115)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (2123)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f100,f112,f117,f146,f226,f233,f237,f238])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK1 = sK2),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    spl7_6 | ~spl7_8 | ~spl7_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f234])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    $false | (spl7_6 | ~spl7_8 | ~spl7_19)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f107,f232,f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1)) ) | ~spl7_8),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1) | r1_tarski(sK1,X1)) ) | ~spl7_8),
% 0.21/0.53    inference(superposition,[],[f32,f163])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (sK0 = sK4(sK1,X0) | r1_tarski(sK1,X0)) ) | ~spl7_8),
% 0.21/0.53    inference(resolution,[],[f128,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK1) | sK0 = X4) ) | ~spl7_8),
% 0.21/0.53    inference(superposition,[],[f64,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl7_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl7_8 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 0.21/0.53    inference(equality_resolution,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    r2_hidden(sK0,sK2) | ~spl7_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    spl7_19 <=> r2_hidden(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK2) | spl7_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl7_6 <=> r1_tarski(sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    spl7_3 | spl7_19 | ~spl7_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f228,f223,f230,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl7_3 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    spl7_18 <=> sK0 = sK3(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl7_18),
% 0.21/0.53    inference(superposition,[],[f25,f225])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    sK0 = sK3(sK2) | ~spl7_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f223])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    spl7_3 | spl7_18 | ~spl7_8 | ~spl7_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f206,f143,f114,f223,f83])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl7_11 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | (~spl7_8 | ~spl7_11)),
% 0.21/0.53    inference(resolution,[],[f204,f25])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK2) | sK0 = X1) ) | (~spl7_8 | ~spl7_11)),
% 0.21/0.53    inference(resolution,[],[f202,f128])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) ) | ~spl7_11),
% 0.21/0.53    inference(condensation,[],[f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,X1)) ) | ~spl7_11),
% 0.21/0.53    inference(resolution,[],[f193,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(X2,sK1)) | ~r2_hidden(X3,sK2)) ) | ~spl7_11),
% 0.21/0.53    inference(superposition,[],[f70,f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,sK1) = k4_xboole_0(k4_xboole_0(X0,sK1),sK2)) ) | ~spl7_11),
% 0.21/0.53    inference(superposition,[],[f63,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl7_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f143])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f50])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl7_11 | ~spl7_4 | ~spl7_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f119,f114,f88,f143])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl7_4 <=> k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | (~spl7_4 | ~spl7_8)),
% 0.21/0.53    inference(backward_demodulation,[],[f90,f116])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f88])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl7_2 | spl7_8 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f101,f97,f114,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl7_5 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | ~spl7_5),
% 0.21/0.53    inference(resolution,[],[f99,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f52,f52])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ~spl7_6 | spl7_7 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f92,f88,f109,f105])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl7_7 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl7_4),
% 0.21/0.53    inference(superposition,[],[f90,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f29,f51])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl7_5 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f95,f88,f97])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl7_4),
% 0.21/0.53    inference(superposition,[],[f54,f90])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f51])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f88])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f51,f52])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f23,f83])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ~spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f22,f78])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f21,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl7_1 <=> sK1 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    sK1 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2123)------------------------------
% 0.21/0.53  % (2123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2123)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2123)Memory used [KB]: 10874
% 0.21/0.53  % (2123)Time elapsed: 0.021 s
% 0.21/0.53  % (2123)------------------------------
% 0.21/0.53  % (2123)------------------------------
% 0.21/0.53  % (2097)Success in time 0.171 s
%------------------------------------------------------------------------------
