%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 193 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  288 ( 478 expanded)
%              Number of equality atoms :   79 ( 136 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f58,f70,f74,f78,f97,f105,f116,f120,f124,f130,f159,f193,f222,f247,f393,f498,f605,f634])).

fof(f634,plain,
    ( spl2_25
    | ~ spl2_38
    | ~ spl2_48 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | spl2_25
    | ~ spl2_38
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f221,f616])).

fof(f616,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_38
    | ~ spl2_48 ),
    inference(superposition,[],[f604,f497])).

fof(f497,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl2_38
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f604,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl2_48
  <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f221,plain,
    ( sK0 != k2_xboole_0(sK0,sK1)
    | spl2_25 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl2_25
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f605,plain,
    ( spl2_48
    | ~ spl2_6
    | ~ spl2_27
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f414,f391,f245,f68,f603])).

fof(f68,plain,
    ( spl2_6
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f245,plain,
    ( spl2_27
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f391,plain,
    ( spl2_35
  <=> ! [X5,X7,X6] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f414,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl2_6
    | ~ spl2_27
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f400,f69])).

fof(f69,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f400,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_27
    | ~ spl2_35 ),
    inference(superposition,[],[f392,f246])).

fof(f246,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f245])).

fof(f392,plain,
    ( ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f391])).

fof(f498,plain,
    ( spl2_38
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f177,f127,f118,f114,f44,f495])).

fof(f44,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f118,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f127,plain,
    ( spl2_18
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f177,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f176,f145])).

fof(f145,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f139,f135])).

fof(f135,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f46,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f139,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f46,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f176,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f171,f135])).

fof(f171,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f129,f115])).

fof(f129,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f393,plain,
    ( spl2_35
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f153,f122,f95,f391])).

fof(f95,plain,
    ( spl2_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f122,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f153,plain,
    ( ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(superposition,[],[f96,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f96,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f247,plain,
    ( spl2_27
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f91,f76,f72,f245])).

fof(f72,plain,
    ( spl2_7
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f76,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f91,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(superposition,[],[f73,f77])).

fof(f77,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f73,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f222,plain,
    ( ~ spl2_1
    | ~ spl2_25
    | ~ spl2_1
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f198,f190,f157,f127,f114,f95,f76,f55,f44,f219,f44])).

fof(f55,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f157,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f190,plain,
    ( spl2_21
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f198,plain,
    ( sK0 != k2_xboole_0(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f165,f194])).

fof(f194,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_18
    | ~ spl2_21 ),
    inference(superposition,[],[f129,f192])).

fof(f192,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f165,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | sK0 != k2_xboole_0(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f164,f135])).

fof(f164,plain,
    ( sK0 != k2_xboole_0(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f163,f77])).

fof(f163,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f162,f96])).

fof(f162,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f161,f135])).

fof(f161,plain,
    ( sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl2_3
    | ~ spl2_20 ),
    inference(superposition,[],[f57,f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f57,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f193,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f135,f114,f44,f190])).

fof(f159,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f41,f157])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f130,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f125,f103,f44,f127])).

fof(f103,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f125,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f46,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f124,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f40,f122])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f120,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f38,f118])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f116,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f37,f114])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f105,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f36,f103])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f97,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f78,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f74,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f70,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f53,f49,f55])).

fof(f49,plain,
    ( spl2_2
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f53,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_2 ),
    inference(forward_demodulation,[],[f51,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f52,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f47,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:49:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (8319)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (8322)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (8316)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (8317)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (8324)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (8321)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (8329)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (8327)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (8314)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (8318)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (8315)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (8328)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (8319)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f638,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f47,f52,f58,f70,f74,f78,f97,f105,f116,f120,f124,f130,f159,f193,f222,f247,f393,f498,f605,f634])).
% 0.20/0.49  fof(f634,plain,(
% 0.20/0.49    spl2_25 | ~spl2_38 | ~spl2_48),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f633])).
% 0.20/0.49  fof(f633,plain,(
% 0.20/0.49    $false | (spl2_25 | ~spl2_38 | ~spl2_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f221,f616])).
% 0.20/0.49  fof(f616,plain,(
% 0.20/0.49    sK0 = k2_xboole_0(sK0,sK1) | (~spl2_38 | ~spl2_48)),
% 0.20/0.49    inference(superposition,[],[f604,f497])).
% 0.20/0.49  fof(f497,plain,(
% 0.20/0.49    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f495])).
% 0.20/0.49  fof(f495,plain,(
% 0.20/0.49    spl2_38 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.49  fof(f604,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | ~spl2_48),
% 0.20/0.49    inference(avatar_component_clause,[],[f603])).
% 0.20/0.49  fof(f603,plain,(
% 0.20/0.49    spl2_48 <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    sK0 != k2_xboole_0(sK0,sK1) | spl2_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f219])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    spl2_25 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.49  fof(f605,plain,(
% 0.20/0.49    spl2_48 | ~spl2_6 | ~spl2_27 | ~spl2_35),
% 0.20/0.49    inference(avatar_split_clause,[],[f414,f391,f245,f68,f603])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl2_6 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    spl2_27 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.49  fof(f391,plain,(
% 0.20/0.49    spl2_35 <=> ! [X5,X7,X6] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.20/0.49  fof(f414,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | (~spl2_6 | ~spl2_27 | ~spl2_35)),
% 0.20/0.49    inference(forward_demodulation,[],[f400,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f400,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl2_27 | ~spl2_35)),
% 0.20/0.49    inference(superposition,[],[f392,f246])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl2_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f245])).
% 0.20/0.49  fof(f392,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | ~spl2_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f391])).
% 0.20/0.49  fof(f498,plain,(
% 0.20/0.49    spl2_38 | ~spl2_1 | ~spl2_15 | ~spl2_16 | ~spl2_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f177,f127,f118,f114,f44,f495])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl2_15 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    spl2_16 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl2_18 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_15 | ~spl2_16 | ~spl2_18)),
% 0.20/0.49    inference(forward_demodulation,[],[f176,f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_15 | ~spl2_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f139,f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl2_1 | ~spl2_15)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f46,f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f44])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | (~spl2_1 | ~spl2_16)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f46,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f118])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_15 | ~spl2_18)),
% 0.20/0.49    inference(forward_demodulation,[],[f171,f135])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) | (~spl2_15 | ~spl2_18)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f129,f115])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f127])).
% 0.20/0.49  fof(f393,plain,(
% 0.20/0.49    spl2_35 | ~spl2_11 | ~spl2_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f153,f122,f95,f391])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl2_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl2_17 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | (~spl2_11 | ~spl2_17)),
% 0.20/0.49    inference(superposition,[],[f96,f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f122])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f95])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    spl2_27 | ~spl2_7 | ~spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f91,f76,f72,f245])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl2_7 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl2_7 | ~spl2_8)),
% 0.20/0.49    inference(superposition,[],[f73,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    ~spl2_1 | ~spl2_25 | ~spl2_1 | spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_15 | ~spl2_18 | ~spl2_20 | ~spl2_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f198,f190,f157,f127,f114,f95,f76,f55,f44,f219,f44])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl2_20 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl2_21 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    sK0 != k2_xboole_0(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl2_1 | spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_15 | ~spl2_18 | ~spl2_20 | ~spl2_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f165,f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl2_18 | ~spl2_21)),
% 0.20/0.49    inference(superposition,[],[f129,f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f190])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | sK0 != k2_xboole_0(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl2_1 | spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_15 | ~spl2_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f164,f135])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    sK0 != k2_xboole_0(sK0,sK1) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl2_1 | spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_15 | ~spl2_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f163,f77])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl2_1 | spl2_3 | ~spl2_11 | ~spl2_15 | ~spl2_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f162,f96])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl2_1 | spl2_3 | ~spl2_15 | ~spl2_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f161,f135])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl2_3 | ~spl2_20)),
% 0.20/0.49    inference(superposition,[],[f57,f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl2_21 | ~spl2_1 | ~spl2_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f135,f114,f44,f190])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl2_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f157])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl2_18 | ~spl2_1 | ~spl2_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f125,f103,f44,f127])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl2_13 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl2_1 | ~spl2_13)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f46,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl2_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f122])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl2_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f118])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl2_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f114])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl2_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f103])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl2_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f95])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f76])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl2_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f72])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl2_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f68])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~spl2_3 | spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f49,f55])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl2_2 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_2),
% 0.20/0.49    inference(forward_demodulation,[],[f51,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f49])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f16])).
% 0.20/0.49  fof(f16,conjecture,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f44])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (8319)------------------------------
% 0.20/0.49  % (8319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8319)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (8319)Memory used [KB]: 6652
% 0.20/0.49  % (8319)Time elapsed: 0.075 s
% 0.20/0.49  % (8319)------------------------------
% 0.20/0.49  % (8319)------------------------------
% 0.20/0.49  % (8320)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (8313)Success in time 0.141 s
%------------------------------------------------------------------------------
