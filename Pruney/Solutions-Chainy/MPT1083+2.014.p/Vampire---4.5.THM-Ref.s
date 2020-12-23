%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 220 expanded)
%              Number of leaves         :   37 (  94 expanded)
%              Depth                    :    6
%              Number of atoms          :  417 ( 757 expanded)
%              Number of equality atoms :   50 (  90 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f103,f107,f121,f132,f137,f141,f151,f162,f166,f171,f175,f188,f203,f218,f221,f224])).

fof(f224,plain,
    ( ~ spl3_1
    | ~ spl3_12
    | spl3_27
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_12
    | spl3_27
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f222,f206])).

fof(f206,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f204,f50])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f204,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_33 ),
    inference(superposition,[],[f202,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f202,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_33
  <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f222,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK0)
    | spl3_27
    | ~ spl3_35 ),
    inference(backward_demodulation,[],[f170,f214])).

fof(f214,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl3_35
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f170,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k1_relat_1(sK1))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_27
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f221,plain,
    ( ~ spl3_7
    | ~ spl3_15
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_15
    | spl3_36 ),
    inference(unit_resulting_resolution,[],[f74,f217,f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f217,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl3_36
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f218,plain,
    ( ~ spl3_23
    | spl3_35
    | ~ spl3_36
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f190,f186,f135,f216,f213,f143])).

fof(f143,plain,
    ( spl3_23
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f135,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f186,plain,
    ( spl3_30
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f190,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | sK0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(resolution,[],[f187,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,X0)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f187,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f203,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_20
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f177,f164,f130,f49,f201])).

fof(f130,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f164,plain,
    ( spl3_26
  <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f177,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_20
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f176,f50])).

fof(f176,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_20
    | ~ spl3_26 ),
    inference(superposition,[],[f131,f165])).

fof(f165,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f164])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f188,plain,
    ( spl3_30
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f180,f173,f73,f69,f57,f186])).

fof(f57,plain,
    ( spl3_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( spl3_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f173,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK0)
        | v1_partfun1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f180,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f179,f70])).

fof(f70,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f179,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f178,f58])).

fof(f58,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f178,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(resolution,[],[f174,f74])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK0)
        | v1_partfun1(X0,X1) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl3_28
    | spl3_4
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f167,f160,f61,f173])).

fof(f61,plain,
    ( spl3_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f160,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK0)
        | v1_partfun1(X0,X1) )
    | spl3_4
    | ~ spl3_25 ),
    inference(resolution,[],[f161,f62])).

fof(f62,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f160])).

fof(f171,plain,
    ( ~ spl3_23
    | ~ spl3_27
    | ~ spl3_1
    | spl3_8
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f156,f139,f77,f49,f169,f143])).

fof(f77,plain,
    ( spl3_8
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f139,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f156,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_1
    | spl3_8
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f154,f50])).

fof(f154,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl3_8
    | ~ spl3_22 ),
    inference(superposition,[],[f78,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f78,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f166,plain,
    ( spl3_26
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f123,f119,f89,f164])).

fof(f89,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f119,plain,
    ( spl3_18
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f123,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(resolution,[],[f120,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f120,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f162,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f38,f160])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f151,plain,
    ( ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f82,f74,f144,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f144,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f143])).

fof(f82,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_9
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f141,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f35,f139])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f137,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f44,f135])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f132,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f39,f130])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f121,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f117,f101,f65,f49,f119])).

fof(f65,plain,
    ( spl3_5
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f117,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f116,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f102,f66])).

fof(f66,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(X1,X0)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f107,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f103,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f95,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f93])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f91,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f87,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f83,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f79,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:33:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (6716)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.45  % (6716)Refutation not found, incomplete strategy% (6716)------------------------------
% 0.19/0.45  % (6716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (6716)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (6716)Memory used [KB]: 6140
% 0.19/0.45  % (6716)Time elapsed: 0.061 s
% 0.19/0.45  % (6716)------------------------------
% 0.19/0.45  % (6716)------------------------------
% 0.19/0.46  % (6724)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (6724)Refutation not found, incomplete strategy% (6724)------------------------------
% 0.19/0.46  % (6724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (6724)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (6724)Memory used [KB]: 10618
% 0.19/0.46  % (6724)Time elapsed: 0.071 s
% 0.19/0.46  % (6724)------------------------------
% 0.19/0.46  % (6724)------------------------------
% 0.19/0.49  % (6713)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.50  % (6705)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (6705)Refutation not found, incomplete strategy% (6705)------------------------------
% 0.19/0.51  % (6705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (6705)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (6705)Memory used [KB]: 10618
% 0.19/0.51  % (6705)Time elapsed: 0.111 s
% 0.19/0.51  % (6705)------------------------------
% 0.19/0.51  % (6705)------------------------------
% 0.19/0.51  % (6717)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.51  % (6718)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.51  % (6709)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (6710)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.51  % (6708)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.51  % (6711)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.52  % (6704)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (6713)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f225,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f51,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f103,f107,f121,f132,f137,f141,f151,f162,f166,f171,f175,f188,f203,f218,f221,f224])).
% 0.19/0.52  fof(f224,plain,(
% 0.19/0.52    ~spl3_1 | ~spl3_12 | spl3_27 | ~spl3_33 | ~spl3_35),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f223])).
% 0.19/0.52  fof(f223,plain,(
% 0.19/0.52    $false | (~spl3_1 | ~spl3_12 | spl3_27 | ~spl3_33 | ~spl3_35)),
% 0.19/0.52    inference(subsumption_resolution,[],[f222,f206])).
% 0.19/0.52  fof(f206,plain,(
% 0.19/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_12 | ~spl3_33)),
% 0.19/0.52    inference(subsumption_resolution,[],[f204,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    v1_relat_1(sK2) | ~spl3_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    spl3_1 <=> v1_relat_1(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.52  fof(f204,plain,(
% 0.19/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | (~spl3_12 | ~spl3_33)),
% 0.19/0.52    inference(superposition,[],[f202,f94])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.19/0.52    inference(avatar_component_clause,[],[f93])).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    spl3_12 <=> ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.52  fof(f202,plain,(
% 0.19/0.52    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_33),
% 0.19/0.52    inference(avatar_component_clause,[],[f201])).
% 0.19/0.52  fof(f201,plain,(
% 0.19/0.52    spl3_33 <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.19/0.52  fof(f222,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k10_relat_1(sK2,sK0) | (spl3_27 | ~spl3_35)),
% 0.19/0.52    inference(backward_demodulation,[],[f170,f214])).
% 0.19/0.52  fof(f214,plain,(
% 0.19/0.52    sK0 = k1_relat_1(sK1) | ~spl3_35),
% 0.19/0.52    inference(avatar_component_clause,[],[f213])).
% 0.19/0.52  fof(f213,plain,(
% 0.19/0.52    spl3_35 <=> sK0 = k1_relat_1(sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.19/0.52  fof(f170,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k10_relat_1(sK2,k1_relat_1(sK1)) | spl3_27),
% 0.19/0.52    inference(avatar_component_clause,[],[f169])).
% 0.19/0.52  fof(f169,plain,(
% 0.19/0.52    spl3_27 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.19/0.52  fof(f221,plain,(
% 0.19/0.52    ~spl3_7 | ~spl3_15 | spl3_36),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f219])).
% 0.19/0.52  fof(f219,plain,(
% 0.19/0.52    $false | (~spl3_7 | ~spl3_15 | spl3_36)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f74,f217,f106])).
% 0.19/0.52  fof(f106,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_15),
% 0.19/0.52    inference(avatar_component_clause,[],[f105])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    spl3_15 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.52  fof(f217,plain,(
% 0.19/0.52    ~v4_relat_1(sK1,sK0) | spl3_36),
% 0.19/0.52    inference(avatar_component_clause,[],[f216])).
% 0.19/0.52  fof(f216,plain,(
% 0.19/0.52    spl3_36 <=> v4_relat_1(sK1,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 0.19/0.52    inference(avatar_component_clause,[],[f73])).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.52  fof(f218,plain,(
% 0.19/0.52    ~spl3_23 | spl3_35 | ~spl3_36 | ~spl3_21 | ~spl3_30),
% 0.19/0.52    inference(avatar_split_clause,[],[f190,f186,f135,f216,f213,f143])).
% 0.19/0.52  fof(f143,plain,(
% 0.19/0.52    spl3_23 <=> v1_relat_1(sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    spl3_21 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.19/0.52  fof(f186,plain,(
% 0.19/0.52    spl3_30 <=> v1_partfun1(sK1,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.19/0.52  fof(f190,plain,(
% 0.19/0.52    ~v4_relat_1(sK1,sK0) | sK0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | (~spl3_21 | ~spl3_30)),
% 0.19/0.52    inference(resolution,[],[f187,f136])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) ) | ~spl3_21),
% 0.19/0.52    inference(avatar_component_clause,[],[f135])).
% 0.19/0.52  fof(f187,plain,(
% 0.19/0.52    v1_partfun1(sK1,sK0) | ~spl3_30),
% 0.19/0.52    inference(avatar_component_clause,[],[f186])).
% 0.19/0.52  fof(f203,plain,(
% 0.19/0.52    spl3_33 | ~spl3_1 | ~spl3_20 | ~spl3_26),
% 0.19/0.52    inference(avatar_split_clause,[],[f177,f164,f130,f49,f201])).
% 0.19/0.52  fof(f130,plain,(
% 0.19/0.52    spl3_20 <=> ! [X1,X0] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.19/0.52  fof(f164,plain,(
% 0.19/0.52    spl3_26 <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.19/0.52  fof(f177,plain,(
% 0.19/0.52    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_20 | ~spl3_26)),
% 0.19/0.52    inference(subsumption_resolution,[],[f176,f50])).
% 0.19/0.52  fof(f176,plain,(
% 0.19/0.52    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_20 | ~spl3_26)),
% 0.19/0.52    inference(superposition,[],[f131,f165])).
% 0.19/0.52  fof(f165,plain,(
% 0.19/0.52    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) | ~spl3_26),
% 0.19/0.52    inference(avatar_component_clause,[],[f164])).
% 0.19/0.52  fof(f131,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) ) | ~spl3_20),
% 0.19/0.52    inference(avatar_component_clause,[],[f130])).
% 0.19/0.52  fof(f188,plain,(
% 0.19/0.52    spl3_30 | ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_28),
% 0.19/0.52    inference(avatar_split_clause,[],[f180,f173,f73,f69,f57,f186])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    spl3_3 <=> v1_funct_1(sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    spl3_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.52  fof(f173,plain,(
% 0.19/0.52    spl3_28 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK0) | v1_partfun1(X0,X1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.19/0.52  fof(f180,plain,(
% 0.19/0.52    v1_partfun1(sK1,sK0) | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_28)),
% 0.19/0.52    inference(subsumption_resolution,[],[f179,f70])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    v1_funct_2(sK1,sK0,sK0) | ~spl3_6),
% 0.19/0.52    inference(avatar_component_clause,[],[f69])).
% 0.19/0.52  fof(f179,plain,(
% 0.19/0.52    ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0) | (~spl3_3 | ~spl3_7 | ~spl3_28)),
% 0.19/0.52    inference(subsumption_resolution,[],[f178,f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    v1_funct_1(sK1) | ~spl3_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f57])).
% 0.19/0.52  fof(f178,plain,(
% 0.19/0.52    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0) | (~spl3_7 | ~spl3_28)),
% 0.19/0.52    inference(resolution,[],[f174,f74])).
% 0.19/0.52  fof(f174,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK0) | v1_partfun1(X0,X1)) ) | ~spl3_28),
% 0.19/0.52    inference(avatar_component_clause,[],[f173])).
% 0.19/0.52  fof(f175,plain,(
% 0.19/0.52    spl3_28 | spl3_4 | ~spl3_25),
% 0.19/0.52    inference(avatar_split_clause,[],[f167,f160,f61,f173])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    spl3_4 <=> v1_xboole_0(sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.52  fof(f160,plain,(
% 0.19/0.52    spl3_25 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.19/0.52  fof(f167,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK0) | v1_partfun1(X0,X1)) ) | (spl3_4 | ~spl3_25)),
% 0.19/0.52    inference(resolution,[],[f161,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ~v1_xboole_0(sK0) | spl3_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f61])).
% 0.19/0.52  fof(f161,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl3_25),
% 0.19/0.52    inference(avatar_component_clause,[],[f160])).
% 0.19/0.52  fof(f171,plain,(
% 0.19/0.52    ~spl3_23 | ~spl3_27 | ~spl3_1 | spl3_8 | ~spl3_22),
% 0.19/0.52    inference(avatar_split_clause,[],[f156,f139,f77,f49,f169,f143])).
% 0.19/0.52  fof(f77,plain,(
% 0.19/0.52    spl3_8 <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    spl3_22 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.19/0.52  fof(f156,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k10_relat_1(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_1 | spl3_8 | ~spl3_22)),
% 0.19/0.52    inference(subsumption_resolution,[],[f154,f50])).
% 0.19/0.52  fof(f154,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k10_relat_1(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | (spl3_8 | ~spl3_22)),
% 0.19/0.52    inference(superposition,[],[f78,f140])).
% 0.19/0.52  fof(f140,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_22),
% 0.19/0.52    inference(avatar_component_clause,[],[f139])).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) | spl3_8),
% 0.19/0.52    inference(avatar_component_clause,[],[f77])).
% 0.19/0.52  fof(f166,plain,(
% 0.19/0.52    spl3_26 | ~spl3_11 | ~spl3_18),
% 0.19/0.52    inference(avatar_split_clause,[],[f123,f119,f89,f164])).
% 0.19/0.52  fof(f89,plain,(
% 0.19/0.52    spl3_11 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.52  fof(f119,plain,(
% 0.19/0.52    spl3_18 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.52  fof(f123,plain,(
% 0.19/0.52    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) | (~spl3_11 | ~spl3_18)),
% 0.19/0.52    inference(resolution,[],[f120,f90])).
% 0.19/0.52  fof(f90,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_11),
% 0.19/0.52    inference(avatar_component_clause,[],[f89])).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK2),sK0) | ~spl3_18),
% 0.19/0.52    inference(avatar_component_clause,[],[f119])).
% 0.19/0.52  fof(f162,plain,(
% 0.19/0.52    spl3_25),
% 0.19/0.52    inference(avatar_split_clause,[],[f38,f160])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.52    inference(flattening,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.52  fof(f151,plain,(
% 0.19/0.52    ~spl3_7 | ~spl3_9 | ~spl3_10 | spl3_23),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f149])).
% 0.19/0.52  fof(f149,plain,(
% 0.19/0.52    $false | (~spl3_7 | ~spl3_9 | ~spl3_10 | spl3_23)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f82,f74,f144,f86])).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_10),
% 0.19/0.52    inference(avatar_component_clause,[],[f85])).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    spl3_10 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.52  fof(f144,plain,(
% 0.19/0.52    ~v1_relat_1(sK1) | spl3_23),
% 0.19/0.52    inference(avatar_component_clause,[],[f143])).
% 0.19/0.52  fof(f82,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_9),
% 0.19/0.52    inference(avatar_component_clause,[],[f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    spl3_9 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.52  fof(f141,plain,(
% 0.19/0.52    spl3_22),
% 0.19/0.52    inference(avatar_split_clause,[],[f35,f139])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.19/0.52  fof(f137,plain,(
% 0.19/0.52    spl3_21),
% 0.19/0.52    inference(avatar_split_clause,[],[f44,f135])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    spl3_20),
% 0.19/0.52    inference(avatar_split_clause,[],[f39,f130])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.19/0.52  fof(f121,plain,(
% 0.19/0.52    spl3_18 | ~spl3_1 | ~spl3_5 | ~spl3_14),
% 0.19/0.52    inference(avatar_split_clause,[],[f117,f101,f65,f49,f119])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    spl3_5 <=> v5_relat_1(sK2,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    spl3_14 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.52  fof(f117,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK2),sK0) | (~spl3_1 | ~spl3_5 | ~spl3_14)),
% 0.19/0.52    inference(subsumption_resolution,[],[f116,f50])).
% 0.19/0.52  fof(f116,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | (~spl3_5 | ~spl3_14)),
% 0.19/0.52    inference(resolution,[],[f102,f66])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    v5_relat_1(sK2,sK0) | ~spl3_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f65])).
% 0.19/0.52  fof(f102,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_14),
% 0.19/0.52    inference(avatar_component_clause,[],[f101])).
% 0.19/0.52  fof(f107,plain,(
% 0.19/0.52    spl3_15),
% 0.19/0.52    inference(avatar_split_clause,[],[f45,f105])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.52  fof(f103,plain,(
% 0.19/0.52    spl3_14),
% 0.19/0.52    inference(avatar_split_clause,[],[f41,f101])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.52  fof(f95,plain,(
% 0.19/0.52    spl3_12),
% 0.19/0.52    inference(avatar_split_clause,[],[f34,f93])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    spl3_11),
% 0.19/0.52    inference(avatar_split_clause,[],[f42,f89])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.52  fof(f87,plain,(
% 0.19/0.52    spl3_10),
% 0.19/0.52    inference(avatar_split_clause,[],[f36,f85])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.52  fof(f83,plain,(
% 0.19/0.52    spl3_9),
% 0.19/0.52    inference(avatar_split_clause,[],[f37,f81])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.52  fof(f79,plain,(
% 0.19/0.52    ~spl3_8),
% 0.19/0.52    inference(avatar_split_clause,[],[f29,f77])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.52    inference(flattening,[],[f13])).
% 0.19/0.52  fof(f13,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,negated_conjecture,(
% 0.19/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.19/0.52    inference(negated_conjecture,[],[f11])).
% 0.19/0.52  fof(f11,conjecture,(
% 0.19/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).
% 0.19/0.52  fof(f75,plain,(
% 0.19/0.52    spl3_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f32,f73])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    spl3_6),
% 0.19/0.52    inference(avatar_split_clause,[],[f31,f69])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    spl3_5),
% 0.19/0.52    inference(avatar_split_clause,[],[f27,f65])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    v5_relat_1(sK2,sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ~spl3_4),
% 0.19/0.52    inference(avatar_split_clause,[],[f33,f61])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ~v1_xboole_0(sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    spl3_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f30,f57])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    v1_funct_1(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    spl3_1),
% 0.19/0.52    inference(avatar_split_clause,[],[f26,f49])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    v1_relat_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (6713)------------------------------
% 0.19/0.52  % (6713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (6713)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (6713)Memory used [KB]: 10746
% 0.19/0.52  % (6713)Time elapsed: 0.122 s
% 0.19/0.52  % (6713)------------------------------
% 0.19/0.52  % (6713)------------------------------
% 0.19/0.52  % (6707)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.52  % (6703)Success in time 0.176 s
%------------------------------------------------------------------------------
