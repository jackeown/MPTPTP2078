%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 258 expanded)
%              Number of leaves         :   38 ( 119 expanded)
%              Depth                    :    7
%              Number of atoms          :  431 ( 748 expanded)
%              Number of equality atoms :  124 ( 242 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f69,f73,f77,f81,f85,f89,f99,f103,f120,f124,f128,f140,f144,f156,f170,f174,f199,f204,f243,f312,f321,f346,f353,f386,f411,f421,f432,f444])).

fof(f444,plain,
    ( ~ spl3_8
    | ~ spl3_17
    | ~ spl3_30
    | spl3_48
    | ~ spl3_52 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_30
    | spl3_48
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f442,f203])).

fof(f203,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl3_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f442,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_17
    | spl3_48
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f441,f84])).

fof(f84,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_8
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f441,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_17
    | spl3_48
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f435,f410])).

fof(f410,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl3_48
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f435,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_17
    | ~ spl3_52 ),
    inference(superposition,[],[f123,f431])).

fof(f431,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl3_52
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f432,plain,
    ( spl3_52
    | ~ spl3_44
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f426,f419,f384,f430])).

fof(f384,plain,
    ( spl3_44
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f419,plain,
    ( spl3_50
  <=> ! [X2] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,sK2)
        | ~ v1_funct_2(sK2,k1_xboole_0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f426,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_44
    | ~ spl3_50 ),
    inference(resolution,[],[f420,f385])).

fof(f385,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f384])).

fof(f420,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,X2)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,sK2) )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f419])).

fof(f421,plain,
    ( spl3_50
    | ~ spl3_18
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f382,f202,f126,f419])).

fof(f126,plain,
    ( spl3_18
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f382,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,sK2)
        | ~ v1_funct_2(sK2,k1_xboole_0,X2) )
    | ~ spl3_18
    | ~ spl3_30 ),
    inference(resolution,[],[f203,f127])).

fof(f127,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f126])).

fof(f411,plain,
    ( ~ spl3_43
    | ~ spl3_48
    | ~ spl3_3
    | ~ spl3_12
    | spl3_39 ),
    inference(avatar_split_clause,[],[f372,f319,f101,f64,f409,f344])).

fof(f344,plain,
    ( spl3_43
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f64,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f319,plain,
    ( spl3_39
  <=> sK0 = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f372,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_12
    | spl3_39 ),
    inference(backward_demodulation,[],[f334,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f334,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_12
    | spl3_39 ),
    inference(superposition,[],[f320,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f320,plain,
    ( sK0 != k10_relat_1(sK2,k2_relat_1(sK2))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f319])).

fof(f386,plain,
    ( spl3_44
    | ~ spl3_4
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f360,f197,f67,f384])).

fof(f67,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f197,plain,
    ( spl3_29
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f360,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f198,f311])).

fof(f311,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f198,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f197])).

fof(f353,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | spl3_43 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | spl3_43 ),
    inference(unit_resulting_resolution,[],[f80,f72,f345,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f345,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f344])).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f80,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_7
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f346,plain,
    ( ~ spl3_43
    | ~ spl3_12
    | ~ spl3_36
    | spl3_39 ),
    inference(avatar_split_clause,[],[f335,f319,f241,f101,f344])).

fof(f241,plain,
    ( spl3_36
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f335,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_36
    | spl3_39 ),
    inference(subsumption_resolution,[],[f334,f242])).

fof(f242,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f241])).

fof(f321,plain,
    ( ~ spl3_39
    | ~ spl3_5
    | ~ spl3_16
    | spl3_27 ),
    inference(avatar_split_clause,[],[f176,f172,f118,f71,f319])).

fof(f118,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f172,plain,
    ( spl3_27
  <=> sK0 = k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f176,plain,
    ( sK0 != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_16
    | spl3_27 ),
    inference(subsumption_resolution,[],[f175,f72])).

fof(f175,plain,
    ( sK0 != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_16
    | spl3_27 ),
    inference(superposition,[],[f173,f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f173,plain,
    ( sK0 != k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f172])).

fof(f312,plain,
    ( spl3_28
    | spl3_4
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f186,f168,f71,f60,f67,f183])).

fof(f183,plain,
    ( spl3_28
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f60,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f168,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f186,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f177,f72])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_26 ),
    inference(resolution,[],[f169,f61])).

fof(f61,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f168])).

fof(f243,plain,
    ( spl3_36
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f237,f183,f122,f71,f241])).

fof(f237,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f235,f72])).

fof(f235,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(superposition,[],[f184,f123])).

fof(f184,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f183])).

fof(f204,plain,
    ( spl3_30
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f195,f87,f71,f64,f202])).

fof(f87,plain,
    ( spl3_9
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f188,f88])).

fof(f88,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f72,f65])).

fof(f199,plain,
    ( spl3_29
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f187,f64,f60,f197])).

fof(f187,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f61,f65])).

fof(f174,plain,
    ( ~ spl3_27
    | ~ spl3_5
    | ~ spl3_22
    | spl3_24 ),
    inference(avatar_split_clause,[],[f162,f154,f142,f71,f172])).

fof(f142,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f154,plain,
    ( spl3_24
  <=> sK0 = k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f162,plain,
    ( sK0 != k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2))
    | ~ spl3_5
    | ~ spl3_22
    | spl3_24 ),
    inference(subsumption_resolution,[],[f161,f72])).

fof(f161,plain,
    ( sK0 != k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_22
    | spl3_24 ),
    inference(superposition,[],[f155,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f155,plain,
    ( sK0 != k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f154])).

fof(f170,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f42,f168])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f156,plain,
    ( ~ spl3_24
    | ~ spl3_5
    | spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f150,f138,f75,f71,f154])).

fof(f75,plain,
    ( spl3_6
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f138,plain,
    ( spl3_21
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f150,plain,
    ( sK0 != k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f149,f72])).

fof(f149,plain,
    ( sK0 != k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_6
    | ~ spl3_21 ),
    inference(superposition,[],[f76,f139])).

fof(f139,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f76,plain,
    ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f144,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f35,f142])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f140,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f43,f138])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f128,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f51,f126])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f45,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f124,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f34,f122])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f33,f118])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f103,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f27,f101])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f99,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f97])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f89,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f85,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f81,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f77,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

fof(f73,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f22,f67,f64])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (27902)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.43  % (27902)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f445,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f62,f69,f73,f77,f81,f85,f89,f99,f103,f120,f124,f128,f140,f144,f156,f170,f174,f199,f204,f243,f312,f321,f346,f353,f386,f411,f421,f432,f444])).
% 0.20/0.43  fof(f444,plain,(
% 0.20/0.43    ~spl3_8 | ~spl3_17 | ~spl3_30 | spl3_48 | ~spl3_52),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f443])).
% 0.20/0.43  fof(f443,plain,(
% 0.20/0.43    $false | (~spl3_8 | ~spl3_17 | ~spl3_30 | spl3_48 | ~spl3_52)),
% 0.20/0.43    inference(subsumption_resolution,[],[f442,f203])).
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_30),
% 0.20/0.43    inference(avatar_component_clause,[],[f202])).
% 0.20/0.43  fof(f202,plain,(
% 0.20/0.43    spl3_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.43  fof(f442,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_8 | ~spl3_17 | spl3_48 | ~spl3_52)),
% 0.20/0.43    inference(forward_demodulation,[],[f441,f84])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    spl3_8 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f441,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_17 | spl3_48 | ~spl3_52)),
% 0.20/0.43    inference(subsumption_resolution,[],[f435,f410])).
% 0.20/0.43  fof(f410,plain,(
% 0.20/0.43    k1_xboole_0 != k1_relat_1(sK2) | spl3_48),
% 0.20/0.43    inference(avatar_component_clause,[],[f409])).
% 0.20/0.43  fof(f409,plain,(
% 0.20/0.43    spl3_48 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.43  fof(f435,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_17 | ~spl3_52)),
% 0.20/0.43    inference(superposition,[],[f123,f431])).
% 0.20/0.43  fof(f431,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl3_52),
% 0.20/0.43    inference(avatar_component_clause,[],[f430])).
% 0.20/0.43  fof(f430,plain,(
% 0.20/0.43    spl3_52 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl3_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.43  fof(f432,plain,(
% 0.20/0.43    spl3_52 | ~spl3_44 | ~spl3_50),
% 0.20/0.43    inference(avatar_split_clause,[],[f426,f419,f384,f430])).
% 0.20/0.43  fof(f384,plain,(
% 0.20/0.43    spl3_44 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.43  fof(f419,plain,(
% 0.20/0.43    spl3_50 <=> ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,sK2) | ~v1_funct_2(sK2,k1_xboole_0,X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.43  fof(f426,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_44 | ~spl3_50)),
% 0.20/0.43    inference(resolution,[],[f420,f385])).
% 0.20/0.43  fof(f385,plain,(
% 0.20/0.43    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_44),
% 0.20/0.43    inference(avatar_component_clause,[],[f384])).
% 0.20/0.43  fof(f420,plain,(
% 0.20/0.43    ( ! [X2] : (~v1_funct_2(sK2,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,sK2)) ) | ~spl3_50),
% 0.20/0.43    inference(avatar_component_clause,[],[f419])).
% 0.20/0.43  fof(f421,plain,(
% 0.20/0.43    spl3_50 | ~spl3_18 | ~spl3_30),
% 0.20/0.43    inference(avatar_split_clause,[],[f382,f202,f126,f419])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    spl3_18 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.43  fof(f382,plain,(
% 0.20/0.43    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,sK2) | ~v1_funct_2(sK2,k1_xboole_0,X2)) ) | (~spl3_18 | ~spl3_30)),
% 0.20/0.43    inference(resolution,[],[f203,f127])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl3_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f126])).
% 0.20/0.43  fof(f411,plain,(
% 0.20/0.43    ~spl3_43 | ~spl3_48 | ~spl3_3 | ~spl3_12 | spl3_39),
% 0.20/0.43    inference(avatar_split_clause,[],[f372,f319,f101,f64,f409,f344])).
% 0.20/0.43  fof(f344,plain,(
% 0.20/0.43    spl3_43 <=> v1_relat_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl3_3 <=> k1_xboole_0 = sK0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    spl3_12 <=> ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f319,plain,(
% 0.20/0.43    spl3_39 <=> sK0 = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.43  fof(f372,plain,(
% 0.20/0.43    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_12 | spl3_39)),
% 0.20/0.43    inference(backward_demodulation,[],[f334,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    k1_xboole_0 = sK0 | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f64])).
% 0.20/0.43  fof(f334,plain,(
% 0.20/0.43    sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_12 | spl3_39)),
% 0.20/0.43    inference(superposition,[],[f320,f102])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f101])).
% 0.20/0.43  fof(f320,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k2_relat_1(sK2)) | spl3_39),
% 0.20/0.43    inference(avatar_component_clause,[],[f319])).
% 0.20/0.43  fof(f386,plain,(
% 0.20/0.43    spl3_44 | ~spl3_4 | ~spl3_29),
% 0.20/0.43    inference(avatar_split_clause,[],[f360,f197,f67,f384])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl3_4 <=> k1_xboole_0 = sK1),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    spl3_29 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.43  fof(f360,plain,(
% 0.20/0.43    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_4 | ~spl3_29)),
% 0.20/0.43    inference(backward_demodulation,[],[f198,f311])).
% 0.20/0.43  fof(f311,plain,(
% 0.20/0.43    k1_xboole_0 = sK1 | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl3_29),
% 0.20/0.43    inference(avatar_component_clause,[],[f197])).
% 0.20/0.43  fof(f353,plain,(
% 0.20/0.43    ~spl3_5 | ~spl3_7 | ~spl3_11 | spl3_43),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f351])).
% 0.20/0.43  fof(f351,plain,(
% 0.20/0.43    $false | (~spl3_5 | ~spl3_7 | ~spl3_11 | spl3_43)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f80,f72,f345,f98])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f97])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    spl3_11 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.43  fof(f345,plain,(
% 0.20/0.43    ~v1_relat_1(sK2) | spl3_43),
% 0.20/0.43    inference(avatar_component_clause,[],[f344])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f79])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl3_7 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.43  fof(f346,plain,(
% 0.20/0.43    ~spl3_43 | ~spl3_12 | ~spl3_36 | spl3_39),
% 0.20/0.43    inference(avatar_split_clause,[],[f335,f319,f241,f101,f344])).
% 0.20/0.43  fof(f241,plain,(
% 0.20/0.43    spl3_36 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.43  fof(f335,plain,(
% 0.20/0.43    ~v1_relat_1(sK2) | (~spl3_12 | ~spl3_36 | spl3_39)),
% 0.20/0.43    inference(subsumption_resolution,[],[f334,f242])).
% 0.20/0.43  fof(f242,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK2) | ~spl3_36),
% 0.20/0.43    inference(avatar_component_clause,[],[f241])).
% 0.20/0.43  fof(f321,plain,(
% 0.20/0.43    ~spl3_39 | ~spl3_5 | ~spl3_16 | spl3_27),
% 0.20/0.43    inference(avatar_split_clause,[],[f176,f172,f118,f71,f319])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    spl3_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.43  fof(f172,plain,(
% 0.20/0.43    spl3_27 <=> sK0 = k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl3_5 | ~spl3_16 | spl3_27)),
% 0.20/0.43    inference(subsumption_resolution,[],[f175,f72])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl3_16 | spl3_27)),
% 0.20/0.43    inference(superposition,[],[f173,f119])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f118])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2)) | spl3_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f172])).
% 0.20/0.43  fof(f312,plain,(
% 0.20/0.43    spl3_28 | spl3_4 | ~spl3_2 | ~spl3_5 | ~spl3_26),
% 0.20/0.43    inference(avatar_split_clause,[],[f186,f168,f71,f60,f67,f183])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    spl3_28 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f168,plain,(
% 0.20/0.43    spl3_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_2 | ~spl3_5 | ~spl3_26)),
% 0.20/0.43    inference(subsumption_resolution,[],[f177,f72])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl3_2 | ~spl3_26)),
% 0.20/0.43    inference(resolution,[],[f169,f61])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    v1_funct_2(sK2,sK0,sK1) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f60])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_26),
% 0.20/0.43    inference(avatar_component_clause,[],[f168])).
% 0.20/0.43  fof(f243,plain,(
% 0.20/0.43    spl3_36 | ~spl3_5 | ~spl3_17 | ~spl3_28),
% 0.20/0.43    inference(avatar_split_clause,[],[f237,f183,f122,f71,f241])).
% 0.20/0.43  fof(f237,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK2) | (~spl3_5 | ~spl3_17 | ~spl3_28)),
% 0.20/0.43    inference(subsumption_resolution,[],[f235,f72])).
% 0.20/0.43  fof(f235,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl3_17 | ~spl3_28)),
% 0.20/0.43    inference(superposition,[],[f184,f123])).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f183])).
% 0.20/0.43  fof(f204,plain,(
% 0.20/0.43    spl3_30 | ~spl3_3 | ~spl3_5 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f195,f87,f71,f64,f202])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f195,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_5 | ~spl3_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f188,f88])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f87])).
% 0.20/0.43  fof(f188,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl3_3 | ~spl3_5)),
% 0.20/0.43    inference(backward_demodulation,[],[f72,f65])).
% 0.20/0.43  fof(f199,plain,(
% 0.20/0.43    spl3_29 | ~spl3_2 | ~spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f187,f64,f60,f197])).
% 0.20/0.43  fof(f187,plain,(
% 0.20/0.43    v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl3_2 | ~spl3_3)),
% 0.20/0.43    inference(backward_demodulation,[],[f61,f65])).
% 0.20/0.43  fof(f174,plain,(
% 0.20/0.43    ~spl3_27 | ~spl3_5 | ~spl3_22 | spl3_24),
% 0.20/0.43    inference(avatar_split_clause,[],[f162,f154,f142,f71,f172])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    spl3_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    spl3_24 <=> sK0 = k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.43  fof(f162,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2)) | (~spl3_5 | ~spl3_22 | spl3_24)),
% 0.20/0.43    inference(subsumption_resolution,[],[f161,f72])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl3_22 | spl3_24)),
% 0.20/0.43    inference(superposition,[],[f155,f143])).
% 0.20/0.43  fof(f143,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f142])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl3_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f154])).
% 0.20/0.43  fof(f170,plain,(
% 0.20/0.43    spl3_26),
% 0.20/0.43    inference(avatar_split_clause,[],[f42,f168])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(flattening,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    ~spl3_24 | ~spl3_5 | spl3_6 | ~spl3_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f150,f138,f75,f71,f154])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl3_6 <=> sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    spl3_21 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | (~spl3_5 | spl3_6 | ~spl3_21)),
% 0.20/0.43    inference(subsumption_resolution,[],[f149,f72])).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    sK0 != k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl3_6 | ~spl3_21)),
% 0.20/0.43    inference(superposition,[],[f76,f139])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f138])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl3_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f75])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    spl3_22),
% 0.20/0.43    inference(avatar_split_clause,[],[f35,f142])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    spl3_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f43,f138])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    spl3_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f51,f126])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f46,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.43    inference(equality_resolution,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.43    inference(equality_resolution,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    spl3_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f122])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    spl3_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f118])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f101])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    spl3_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f97])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f45,f87])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f44,f83])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f79])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ~spl3_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f75])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.43    inference(negated_conjecture,[],[f10])).
% 0.20/0.43  fof(f10,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f71])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl3_3 | ~spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f67,f64])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f60])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (27902)------------------------------
% 0.20/0.43  % (27902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (27902)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (27902)Memory used [KB]: 10874
% 0.20/0.43  % (27902)Time elapsed: 0.017 s
% 0.20/0.43  % (27902)------------------------------
% 0.20/0.43  % (27902)------------------------------
% 0.20/0.43  % (27886)Success in time 0.073 s
%------------------------------------------------------------------------------
