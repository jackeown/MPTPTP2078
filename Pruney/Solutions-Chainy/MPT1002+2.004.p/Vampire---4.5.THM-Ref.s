%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 207 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :    7
%              Number of atoms          :  367 ( 662 expanded)
%              Number of equality atoms :   74 ( 149 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f59,f63,f67,f71,f75,f79,f87,f91,f95,f113,f119,f127,f130,f138,f145,f151,f162,f166,f170,f180,f186])).

fof(f186,plain,
    ( ~ spl4_10
    | spl4_21
    | ~ spl4_25
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl4_10
    | spl4_21
    | ~ spl4_25
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f184,f161])).

fof(f161,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_25
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f184,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_10
    | spl4_21
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f126,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_10
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f181,f169])).

fof(f169,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f181,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_10
    | ~ spl4_28 ),
    inference(superposition,[],[f179,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f179,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl4_28
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f126,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_21
  <=> r1_tarski(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f180,plain,
    ( spl4_28
    | ~ spl4_14
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f176,f168,f164,f93,f178])).

fof(f93,plain,
    ( spl4_14
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f164,plain,
    ( spl4_26
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f176,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_14
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f172,f165])).

fof(f165,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f164])).

fof(f172,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_14
    | ~ spl4_27 ),
    inference(resolution,[],[f169,f94])).

fof(f94,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f170,plain,
    ( spl4_27
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f155,f61,f54,f168])).

fof(f54,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f61,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f155,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f62,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f166,plain,
    ( spl4_26
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f154,f54,f50,f164])).

fof(f50,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f154,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f51,f55])).

fof(f51,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f162,plain,
    ( spl4_25
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f153,f54,f46,f160])).

fof(f46,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f153,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f47,f55])).

fof(f47,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f151,plain,
    ( ~ spl4_2
    | ~ spl4_6
    | ~ spl4_10
    | spl4_21
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_10
    | spl4_21
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f149,f47])).

fof(f149,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl4_6
    | ~ spl4_10
    | spl4_21
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f126,f148])).

fof(f148,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f146,f62])).

fof(f146,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(superposition,[],[f144,f78])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_24
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f145,plain,
    ( spl4_24
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f141,f136,f61,f57,f50,f143])).

fof(f57,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f136,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f141,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f140,f51])).

fof(f140,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(resolution,[],[f137,f62])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f33,f136])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f130,plain,
    ( ~ spl4_6
    | ~ spl4_8
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f62,f123,f70])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f127,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | ~ spl4_9
    | spl4_19 ),
    inference(avatar_split_clause,[],[f120,f117,f73,f125,f122])).

fof(f73,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f117,plain,
    ( spl4_19
  <=> r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f120,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_19 ),
    inference(resolution,[],[f118,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f118,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( ~ spl4_19
    | ~ spl4_6
    | ~ spl4_13
    | spl4_18 ),
    inference(avatar_split_clause,[],[f115,f111,f89,f61,f117])).

fof(f89,plain,
    ( spl4_13
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f111,plain,
    ( spl4_18
  <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f115,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ spl4_6
    | ~ spl4_13
    | spl4_18 ),
    inference(backward_demodulation,[],[f112,f114])).

fof(f114,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(resolution,[],[f90,f62])).

fof(f90,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f112,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( ~ spl4_18
    | ~ spl4_6
    | spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f105,f85,f65,f61,f111])).

fof(f65,plain,
    ( spl4_7
  <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f85,plain,
    ( spl4_12
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f105,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))
    | ~ spl4_6
    | spl4_7
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f66,f104])).

fof(f104,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f86,f62])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f66,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f95,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f35,f89])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f87,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f79,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f27,f77])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f25,f73])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f71,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

fof(f63,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f19,f57,f54])).

fof(f19,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (18226)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (18217)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (18226)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (18225)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f48,f52,f59,f63,f67,f71,f75,f79,f87,f91,f95,f113,f119,f127,f130,f138,f145,f151,f162,f166,f170,f180,f186])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ~spl4_10 | spl4_21 | ~spl4_25 | ~spl4_27 | ~spl4_28),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f185])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    $false | (~spl4_10 | spl4_21 | ~spl4_25 | ~spl4_27 | ~spl4_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f184,f161])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    r1_tarski(sK2,k1_xboole_0) | ~spl4_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f160])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    spl4_25 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k1_xboole_0) | (~spl4_10 | spl4_21 | ~spl4_27 | ~spl4_28)),
% 0.21/0.46    inference(backward_demodulation,[],[f126,f183])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(sK3) | (~spl4_10 | ~spl4_27 | ~spl4_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f181,f169])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f168])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    spl4_27 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_10 | ~spl4_28)),
% 0.21/0.46    inference(superposition,[],[f179,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl4_10 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl4_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    spl4_28 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    spl4_21 <=> r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.46  fof(f180,plain,(
% 0.21/0.46    spl4_28 | ~spl4_14 | ~spl4_26 | ~spl4_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f176,f168,f164,f93,f178])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl4_14 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    spl4_26 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl4_14 | ~spl4_26 | ~spl4_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f172,f165])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f164])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl4_14 | ~spl4_27)),
% 0.21/0.46    inference(resolution,[],[f169,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl4_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    spl4_27 | ~spl4_4 | ~spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f155,f61,f54,f168])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl4_4 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_4 | ~spl4_6)),
% 0.21/0.46    inference(backward_demodulation,[],[f62,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f61])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    spl4_26 | ~spl4_3 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f154,f54,f50,f164])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl4_3 | ~spl4_4)),
% 0.21/0.46    inference(backward_demodulation,[],[f51,f55])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    spl4_25 | ~spl4_2 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f153,f54,f46,f160])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl4_2 <=> r1_tarski(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.46    inference(backward_demodulation,[],[f47,f55])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    r1_tarski(sK2,sK0) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    ~spl4_2 | ~spl4_6 | ~spl4_10 | spl4_21 | ~spl4_24),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    $false | (~spl4_2 | ~spl4_6 | ~spl4_10 | spl4_21 | ~spl4_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f149,f47])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    ~r1_tarski(sK2,sK0) | (~spl4_6 | ~spl4_10 | spl4_21 | ~spl4_24)),
% 0.21/0.46    inference(backward_demodulation,[],[f126,f148])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f146,f62])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_10 | ~spl4_24)),
% 0.21/0.46    inference(superposition,[],[f144,f78])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f143])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    spl4_24 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    spl4_24 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f141,f136,f61,f57,f50,f143])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl4_5 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    spl4_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f140,f51])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl4_5 | ~spl4_6 | ~spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f139,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    k1_xboole_0 != sK1 | spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (~spl4_6 | ~spl4_23)),
% 0.21/0.46    inference(resolution,[],[f137,f62])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl4_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f136])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    spl4_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f136])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ~spl4_6 | ~spl4_8 | spl4_20),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    $false | (~spl4_6 | ~spl4_8 | spl4_20)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f62,f123,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl4_8 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ~v1_relat_1(sK3) | spl4_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    spl4_20 <=> v1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ~spl4_20 | ~spl4_21 | ~spl4_9 | spl4_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f120,f117,f73,f125,f122])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl4_9 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl4_19 <=> r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | spl4_19)),
% 0.21/0.46    inference(resolution,[],[f118,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | spl4_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f117])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ~spl4_19 | ~spl4_6 | ~spl4_13 | spl4_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f115,f111,f89,f61,f117])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl4_13 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    spl4_18 <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | (~spl4_6 | ~spl4_13 | spl4_18)),
% 0.21/0.46    inference(backward_demodulation,[],[f112,f114])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X0] : (k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)) ) | (~spl4_6 | ~spl4_13)),
% 0.21/0.46    inference(resolution,[],[f90,f62])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl4_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) | spl4_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f111])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ~spl4_18 | ~spl4_6 | spl4_7 | ~spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f105,f85,f65,f61,f111])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl4_7 <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl4_12 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) | (~spl4_6 | spl4_7 | ~spl4_12)),
% 0.21/0.46    inference(backward_demodulation,[],[f66,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | (~spl4_6 | ~spl4_12)),
% 0.21/0.46    inference(resolution,[],[f86,f62])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) ) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) | spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f65])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl4_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f93])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl4_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f89])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f85])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl4_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f77])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl4_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f73])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f69])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ~spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f65])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f61])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl4_4 | ~spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f57,f54])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r1_tarski(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (18226)------------------------------
% 0.21/0.47  % (18226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18226)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (18226)Memory used [KB]: 10618
% 0.21/0.47  % (18226)Time elapsed: 0.012 s
% 0.21/0.47  % (18226)------------------------------
% 0.21/0.47  % (18226)------------------------------
% 0.21/0.47  % (18216)Success in time 0.11 s
%------------------------------------------------------------------------------
