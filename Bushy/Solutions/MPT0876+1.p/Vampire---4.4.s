%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t36_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 422 expanded)
%              Number of leaves         :   36 ( 178 expanded)
%              Depth                    :   10
%              Number of atoms          :  525 (1263 expanded)
%              Number of equality atoms :  231 ( 788 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f53,f60,f67,f86,f108,f130,f135,f143,f144,f157,f161,f166,f168,f180,f187,f192,f203,f211,f212,f213,f214,f219,f231,f241,f245,f254,f262,f270,f330,f332,f333,f344,f354])).

fof(f354,plain,
    ( spl6_9
    | spl6_17
    | ~ spl6_30
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_30
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f352,f73])).

fof(f73,plain,
    ( sK2 != sK5
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_9
  <=> sK2 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f352,plain,
    ( sK2 = sK5
    | ~ spl6_17
    | ~ spl6_30
    | ~ spl6_33 ),
    inference(equality_resolution,[],[f310])).

fof(f310,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(X6,X7) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | sK5 = X7 )
    | ~ spl6_17
    | ~ spl6_30
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f309,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK5
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_17
  <=> k1_xboole_0 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f309,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(X6,X7) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = sK5
        | sK5 = X7 )
    | ~ spl6_30
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f300,f186])).

fof(f186,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_33
  <=> k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f300,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(X6,X7) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = sK5
        | sK5 = X7 )
    | ~ spl6_30 ),
    inference(superposition,[],[f33,f179])).

fof(f179,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK5)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_30
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',t134_zfmisc_1)).

fof(f344,plain,
    ( ~ spl6_45
    | ~ spl6_10
    | spl6_41 ),
    inference(avatar_split_clause,[],[f337,f319,f75,f342])).

fof(f342,plain,
    ( spl6_45
  <=> sK1 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f75,plain,
    ( spl6_10
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f319,plain,
    ( spl6_41
  <=> sK4 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f337,plain,
    ( sK1 != sK5
    | ~ spl6_10
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f320,f76])).

fof(f76,plain,
    ( sK1 = sK4
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f320,plain,
    ( sK4 != sK5
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f319])).

fof(f333,plain,
    ( spl6_10
    | spl6_5
    | spl6_27
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f317,f260,f152,f58,f75])).

fof(f58,plain,
    ( spl6_5
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f152,plain,
    ( spl6_27
  <=> k1_xboole_0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f260,plain,
    ( spl6_36
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f317,plain,
    ( sK1 = sK4
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_36 ),
    inference(equality_resolution,[],[f312])).

fof(f312,plain,
    ( ! [X8,X9] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X8,X9)
        | sK4 = X9 )
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f311,f153])).

fof(f153,plain,
    ( k1_xboole_0 != sK4
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f152])).

fof(f311,plain,
    ( ! [X8,X9] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X8,X9)
        | k1_xboole_0 = sK4
        | sK4 = X9 )
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f301,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f301,plain,
    ( ! [X8,X9] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X8,X9)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK4
        | sK4 = X9 )
    | ~ spl6_36 ),
    inference(superposition,[],[f33,f261])).

fof(f261,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f260])).

fof(f332,plain,
    ( spl6_5
    | spl6_11
    | spl6_27
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_27
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f317,f79])).

fof(f79,plain,
    ( sK1 != sK4
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_11
  <=> sK1 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f330,plain,
    ( spl6_40
    | ~ spl6_43
    | spl6_5
    | spl6_27
    | ~ spl6_30
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f315,f260,f178,f152,f58,f328,f322])).

fof(f322,plain,
    ( spl6_40
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f328,plain,
    ( spl6_43
  <=> k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f315,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | sK4 = sK5
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_30
    | ~ spl6_36 ),
    inference(superposition,[],[f312,f179])).

fof(f270,plain,
    ( spl6_38
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f263,f81,f65,f268])).

fof(f268,plain,
    ( spl6_38
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f65,plain,
    ( spl6_6
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f81,plain,
    ( spl6_12
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f263,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK4),sK5)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f66,f82])).

fof(f82,plain,
    ( sK0 = sK3
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f66,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f262,plain,
    ( spl6_36
    | ~ spl6_12
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f255,f128,f81,f260])).

fof(f128,plain,
    ( spl6_20
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f255,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4)
    | ~ spl6_12
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f129,f82])).

fof(f129,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f128])).

fof(f254,plain,
    ( ~ spl6_35
    | ~ spl6_12
    | spl6_15 ),
    inference(avatar_split_clause,[],[f247,f91,f81,f252])).

fof(f252,plain,
    ( spl6_35
  <=> k1_xboole_0 != k2_zfmisc_1(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f91,plain,
    ( spl6_15
  <=> k1_xboole_0 != k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f247,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK4)
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f92,f82])).

fof(f92,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,sK4)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f91])).

fof(f245,plain,
    ( spl6_15
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f242,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',t113_zfmisc_1)).

fof(f242,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,k1_xboole_0)
    | ~ spl6_15
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f156,f92])).

fof(f156,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_26
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f241,plain,
    ( spl6_3
    | spl6_5
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f239,f59])).

fof(f239,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f236,f52])).

fof(f52,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f236,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_32 ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_32 ),
    inference(superposition,[],[f34,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_32
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f231,plain,
    ( spl6_13
    | ~ spl6_20
    | spl6_25
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f229,f85])).

fof(f85,plain,
    ( sK0 != sK3
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_13
  <=> sK0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f229,plain,
    ( sK0 = sK3
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(equality_resolution,[],[f225])).

fof(f225,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | sK3 = X2 )
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f224,f153])).

fof(f224,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK4
        | sK3 = X2 )
    | ~ spl6_20
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f222,f147])).

fof(f147,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_25
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f222,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK4
        | sK3 = X2 )
    | ~ spl6_20 ),
    inference(superposition,[],[f32,f129])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f219,plain,
    ( ~ spl6_6
    | ~ spl6_16
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f217,f107])).

fof(f107,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_19
  <=> k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f217,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f216,f38])).

fof(f216,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f66,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_16
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f214,plain,
    ( spl6_14
    | spl6_16
    | ~ spl6_19
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f164,f65,f106,f100,f94])).

fof(f94,plain,
    ( spl6_14
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f164,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_6 ),
    inference(superposition,[],[f34,f66])).

fof(f213,plain,
    ( spl6_16
    | spl6_14
    | spl6_22
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f163,f65,f133,f94,f100])).

fof(f133,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k2_zfmisc_1(sK3,sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f163,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
        | k1_xboole_0 = sK5
        | k2_zfmisc_1(sK3,sK4) = X2 )
    | ~ spl6_6 ),
    inference(superposition,[],[f32,f66])).

fof(f212,plain,
    ( spl6_16
    | spl6_14
    | spl6_22
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f109,f65,f133,f94,f100])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
        | k1_xboole_0 = sK5
        | k2_zfmisc_1(sK3,sK4) = X0 )
    | ~ spl6_6 ),
    inference(superposition,[],[f32,f66])).

fof(f211,plain,
    ( spl6_15
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f209,f39])).

fof(f39,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f209,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK4)
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f92,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_24
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f203,plain,
    ( spl6_1
    | ~ spl6_18
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f201,f186])).

fof(f201,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f198,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_1
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f198,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_18 ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_18 ),
    inference(superposition,[],[f34,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_18
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f192,plain,
    ( ~ spl6_33
    | ~ spl6_20
    | spl6_25
    | spl6_27 ),
    inference(avatar_split_clause,[],[f191,f152,f146,f128,f185])).

fof(f191,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f190,f147])).

fof(f190,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f173,f153])).

fof(f173,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_20 ),
    inference(superposition,[],[f34,f129])).

fof(f187,plain,
    ( ~ spl6_33
    | spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f170,f128,f91,f185])).

fof(f170,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(superposition,[],[f92,f129])).

fof(f180,plain,
    ( spl6_30
    | ~ spl6_6
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f169,f128,f65,f178])).

fof(f169,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK5)
    | ~ spl6_6
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f129,f66])).

fof(f168,plain,
    ( spl6_14
    | ~ spl6_19
    | ~ spl6_6
    | spl6_17 ),
    inference(avatar_split_clause,[],[f167,f97,f65,f106,f94])).

fof(f167,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f164,f98])).

fof(f166,plain,
    ( spl6_14
    | spl6_22
    | ~ spl6_6
    | spl6_17 ),
    inference(avatar_split_clause,[],[f165,f97,f65,f133,f94])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
        | k2_zfmisc_1(sK3,sK4) = X2 )
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f163,f98])).

fof(f161,plain,
    ( spl6_26
    | spl6_24
    | spl6_28
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f138,f94,f159,f149,f155])).

fof(f159,plain,
    ( spl6_28
  <=> ! [X3,X2] :
        ( k1_xboole_0 != k2_zfmisc_1(X2,X3)
        | sK3 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f138,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK4
        | sK3 = X2 )
    | ~ spl6_14 ),
    inference(superposition,[],[f32,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f157,plain,
    ( spl6_24
    | spl6_26
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f140,f94,f155,f149])).

fof(f140,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_14 ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_14 ),
    inference(superposition,[],[f34,f95])).

fof(f144,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f141,f94,f65,f103])).

fof(f141,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f136,f39])).

fof(f136,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK5) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f95,f66])).

fof(f143,plain,
    ( ~ spl6_6
    | ~ spl6_14
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f141,f107])).

fof(f135,plain,
    ( spl6_14
    | spl6_22
    | ~ spl6_6
    | spl6_17 ),
    inference(avatar_split_clause,[],[f131,f97,f65,f133,f94])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
        | k2_zfmisc_1(sK3,sK4) = X0 )
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f109,f98])).

fof(f130,plain,
    ( spl6_20
    | ~ spl6_6
    | spl6_15
    | spl6_17 ),
    inference(avatar_split_clause,[],[f123,f97,f91,f65,f128])).

fof(f123,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k2_zfmisc_1(sK3,sK4) = X0 )
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f118,f98])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = sK5
        | k2_zfmisc_1(sK3,sK4) = X0 )
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f109,f92])).

fof(f108,plain,
    ( spl6_14
    | spl6_16
    | ~ spl6_19
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f87,f65,f106,f100,f94])).

fof(f87,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_6 ),
    inference(superposition,[],[f34,f66])).

fof(f86,plain,
    ( ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f24,f84,f78,f72])).

fof(f24,plain,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',t36_mcart_1)).

fof(f67,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f25,f30,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',d3_zfmisc_1)).

fof(f25,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f28,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
