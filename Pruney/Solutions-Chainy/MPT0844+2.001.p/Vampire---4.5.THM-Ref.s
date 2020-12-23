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
% DateTime   : Thu Dec  3 12:58:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 226 expanded)
%              Number of leaves         :   42 ( 108 expanded)
%              Depth                    :    7
%              Number of atoms          :  378 ( 591 expanded)
%              Number of equality atoms :   71 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f767,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f66,f70,f74,f78,f82,f86,f94,f98,f102,f106,f122,f127,f141,f158,f165,f195,f199,f207,f214,f271,f276,f320,f340,f365,f748,f765])).

fof(f765,plain,
    ( ~ spl4_1
    | ~ spl4_9
    | spl4_48
    | ~ spl4_81 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_9
    | spl4_48
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f417,f749])).

fof(f749,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl4_1
    | ~ spl4_81 ),
    inference(unit_resulting_resolution,[],[f51,f747])).

fof(f747,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = k3_xboole_0(X5,X4)
        | ~ r1_xboole_0(X4,X5) )
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl4_81
  <=> ! [X5,X4] :
        ( k1_xboole_0 = k3_xboole_0(X5,X4)
        | ~ r1_xboole_0(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f51,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f417,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,sK1)
    | ~ spl4_9
    | spl4_48 ),
    inference(unit_resulting_resolution,[],[f364,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f364,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl4_48 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl4_48
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f748,plain,
    ( spl4_81
    | ~ spl4_8
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f325,f318,f80,f746])).

% (27774)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f80,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f318,plain,
    ( spl4_42
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f325,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = k3_xboole_0(X5,X4)
        | ~ r1_xboole_0(X4,X5) )
    | ~ spl4_8
    | ~ spl4_42 ),
    inference(superposition,[],[f319,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f319,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f318])).

fof(f365,plain,
    ( ~ spl4_48
    | ~ spl4_35
    | spl4_36
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f342,f338,f273,f268,f362])).

fof(f268,plain,
    ( spl4_35
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f273,plain,
    ( spl4_36
  <=> r1_xboole_0(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f338,plain,
    ( spl4_45
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,X0)
        | r1_xboole_0(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f342,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl4_35
    | spl4_36
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f275,f270,f339])).

fof(f339,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X0)
        | r1_xboole_0(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f338])).

fof(f270,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f268])).

fof(f275,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK1)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f273])).

fof(f340,plain,
    ( spl4_45
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f209,f205,f92,f338])).

fof(f92,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f205,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X0)
        | r1_xboole_0(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(superposition,[],[f93,f206])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f205])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f320,plain,
    ( spl4_42
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f202,f197,f72,f318])).

fof(f72,plain,
    ( spl4_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f197,plain,
    ( spl4_27
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f202,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(superposition,[],[f198,f73])).

fof(f73,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f198,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f197])).

fof(f276,plain,
    ( ~ spl4_36
    | ~ spl4_17
    | ~ spl4_19
    | spl4_26 ),
    inference(avatar_split_clause,[],[f256,f192,f139,f124,f273])).

fof(f124,plain,
    ( spl4_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f139,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f192,plain,
    ( spl4_26
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f256,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl4_17
    | ~ spl4_19
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f126,f194,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f194,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f126,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f271,plain,
    ( spl4_35
    | ~ spl4_17
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f221,f212,f162,f124,f268])).

fof(f162,plain,
    ( spl4_21
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f212,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f221,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_17
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f164,f126,f213])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f212])).

fof(f164,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f162])).

fof(f214,plain,
    ( spl4_29
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f143,f120,f76,f212])).

fof(f76,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f120,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(superposition,[],[f77,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f207,plain,
    ( spl4_28
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f129,f100,f80,f64,f205])).

fof(f64,plain,
    ( spl4_4
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f100,plain,
    ( spl4_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f128,f65])).

fof(f65,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(superposition,[],[f101,f81])).

fof(f101,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f199,plain,
    ( spl4_27
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f111,f72,f68,f197])).

fof(f68,plain,
    ( spl4_5
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f111,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f73,f69])).

fof(f69,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f195,plain,
    ( ~ spl4_2
    | ~ spl4_26
    | spl4_3
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f160,f156,f59,f192,f54])).

fof(f54,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( spl4_3
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f156,plain,
    ( spl4_20
  <=> ! [X1,X3,X0,X2] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f160,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl4_3
    | ~ spl4_20 ),
    inference(superposition,[],[f61,f157])).

fof(f157,plain,
    ( ! [X2,X0,X3,X1] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f61,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f165,plain,
    ( spl4_21
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f130,f104,f54,f162])).

fof(f104,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f130,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f56,f105])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f158,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f47,f156])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f141,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f38,f139])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

% (27771)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f127,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f117,f96,f54,f124])).

fof(f96,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f117,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f56,f97])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f122,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f39,f120])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f106,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f45,f104])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f102,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f35,f100])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f98,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f94,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f86,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f82,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f74,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f70,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f66,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f62,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:16:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (27776)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (27776)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f767,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f52,f57,f62,f66,f70,f74,f78,f82,f86,f94,f98,f102,f106,f122,f127,f141,f158,f165,f195,f199,f207,f214,f271,f276,f320,f340,f365,f748,f765])).
% 0.21/0.47  fof(f765,plain,(
% 0.21/0.47    ~spl4_1 | ~spl4_9 | spl4_48 | ~spl4_81),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f764])).
% 0.21/0.47  fof(f764,plain,(
% 0.21/0.47    $false | (~spl4_1 | ~spl4_9 | spl4_48 | ~spl4_81)),
% 0.21/0.47    inference(subsumption_resolution,[],[f417,f749])).
% 0.21/0.47  fof(f749,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl4_1 | ~spl4_81)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f51,f747])).
% 0.21/0.47  fof(f747,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) ) | ~spl4_81),
% 0.21/0.47    inference(avatar_component_clause,[],[f746])).
% 0.21/0.47  fof(f746,plain,(
% 0.21/0.47    spl4_81 <=> ! [X5,X4] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl4_1 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f417,plain,(
% 0.21/0.47    k1_xboole_0 != k3_xboole_0(sK2,sK1) | (~spl4_9 | spl4_48)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f364,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl4_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl4_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.47  fof(f364,plain,(
% 0.21/0.47    ~r1_xboole_0(sK2,sK1) | spl4_48),
% 0.21/0.47    inference(avatar_component_clause,[],[f362])).
% 0.21/0.47  fof(f362,plain,(
% 0.21/0.47    spl4_48 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.47  fof(f748,plain,(
% 0.21/0.47    spl4_81 | ~spl4_8 | ~spl4_42),
% 0.21/0.47    inference(avatar_split_clause,[],[f325,f318,f80,f746])).
% 0.21/0.47  % (27774)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl4_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    spl4_42 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.47  fof(f325,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) ) | (~spl4_8 | ~spl4_42)),
% 0.21/0.47    inference(superposition,[],[f319,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f80])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl4_42),
% 0.21/0.47    inference(avatar_component_clause,[],[f318])).
% 0.21/0.47  fof(f365,plain,(
% 0.21/0.47    ~spl4_48 | ~spl4_35 | spl4_36 | ~spl4_45),
% 0.21/0.47    inference(avatar_split_clause,[],[f342,f338,f273,f268,f362])).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    spl4_35 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    spl4_36 <=> r1_xboole_0(k1_relat_1(sK3),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.47  fof(f338,plain,(
% 0.21/0.47    spl4_45 <=> ! [X1,X0,X2] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.47  fof(f342,plain,(
% 0.21/0.47    ~r1_xboole_0(sK2,sK1) | (~spl4_35 | spl4_36 | ~spl4_45)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f275,f270,f339])).
% 0.21/0.47  fof(f339,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1)) ) | ~spl4_45),
% 0.21/0.47    inference(avatar_component_clause,[],[f338])).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK2) | ~spl4_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f268])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_relat_1(sK3),sK1) | spl4_36),
% 0.21/0.47    inference(avatar_component_clause,[],[f273])).
% 0.21/0.47  fof(f340,plain,(
% 0.21/0.47    spl4_45 | ~spl4_11 | ~spl4_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f209,f205,f92,f338])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl4_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    spl4_28 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1)) ) | (~spl4_11 | ~spl4_28)),
% 0.21/0.47    inference(superposition,[],[f93,f206])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f205])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    spl4_42 | ~spl4_6 | ~spl4_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f202,f197,f72,f318])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl4_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    spl4_27 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl4_6 | ~spl4_27)),
% 0.21/0.47    inference(superposition,[],[f198,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl4_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f197])).
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    ~spl4_36 | ~spl4_17 | ~spl4_19 | spl4_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f256,f192,f139,f124,f273])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl4_17 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl4_19 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    spl4_26 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_relat_1(sK3),sK1) | (~spl4_17 | ~spl4_19 | spl4_26)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f126,f194,f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(sK3,sK1) | spl4_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f192])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl4_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f124])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    spl4_35 | ~spl4_17 | ~spl4_21 | ~spl4_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f221,f212,f162,f124,f268])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    spl4_21 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    spl4_29 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK2) | (~spl4_17 | ~spl4_21 | ~spl4_29)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f164,f126,f213])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) ) | ~spl4_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f212])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    v4_relat_1(sK3,sK2) | ~spl4_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f162])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    spl4_29 | ~spl4_7 | ~spl4_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f143,f120,f76,f212])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl4_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    spl4_16 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) ) | (~spl4_7 | ~spl4_16)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | (~spl4_7 | ~spl4_16)),
% 0.21/0.47    inference(superposition,[],[f77,f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl4_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f120])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl4_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    spl4_28 | ~spl4_4 | ~spl4_8 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f129,f100,f80,f64,f205])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl4_4 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl4_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | (~spl4_4 | ~spl4_8 | ~spl4_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f128,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | (~spl4_8 | ~spl4_13)),
% 0.21/0.47    inference(superposition,[],[f101,f81])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    spl4_27 | ~spl4_5 | ~spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f111,f72,f68,f197])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl4_5 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.47    inference(superposition,[],[f73,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    ~spl4_2 | ~spl4_26 | spl4_3 | ~spl4_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f160,f156,f59,f192,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl4_3 <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    spl4_20 <=> ! [X1,X3,X0,X2] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | (spl4_3 | ~spl4_20)),
% 0.21/0.47    inference(superposition,[],[f61,f157])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f156])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) | spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    spl4_21 | ~spl4_2 | ~spl4_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f104,f54,f162])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl4_14 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    v4_relat_1(sK3,sK2) | (~spl4_2 | ~spl4_14)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f56,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f104])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl4_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f156])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl4_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f139])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  % (27771)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl4_17 | ~spl4_2 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f96,f54,f124])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl4_12 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v1_relat_1(sK3) | (~spl4_2 | ~spl4_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f56,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl4_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f120])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f104])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f100])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f92])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f84])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f80])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f76])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f72])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f68])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f64])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f59])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f54])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f49])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    r1_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27776)------------------------------
% 0.21/0.48  % (27776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27776)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27776)Memory used [KB]: 6652
% 0.21/0.48  % (27776)Time elapsed: 0.037 s
% 0.21/0.48  % (27776)------------------------------
% 0.21/0.48  % (27776)------------------------------
% 0.21/0.48  % (27779)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (27764)Success in time 0.118 s
%------------------------------------------------------------------------------
