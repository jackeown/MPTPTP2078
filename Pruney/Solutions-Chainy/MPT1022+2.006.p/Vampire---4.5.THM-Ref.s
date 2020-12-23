%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 253 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :  419 ( 763 expanded)
%              Number of equality atoms :   77 ( 142 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f87,f94,f99,f103,f107,f111,f118,f122,f130,f135,f144,f157,f161,f162,f165])).

fof(f165,plain,
    ( ~ spl3_5
    | ~ spl3_18
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_18
    | spl3_19 ),
    inference(subsumption_resolution,[],[f163,f156])).

fof(f156,plain,
    ( sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_18
  <=> sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f163,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ spl3_5
    | spl3_19 ),
    inference(superposition,[],[f160,f70])).

fof(f70,plain,
    ( ! [X0] : k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f160,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_19
  <=> sK1 = k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f162,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f146,f132,f97,f85,f55,f51,f142])).

fof(f142,plain,
    ( spl3_17
  <=> sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f51,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f85,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f97,plain,
    ( spl3_9
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f132,plain,
    ( spl3_16
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f146,plain,
    ( sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(resolution,[],[f139,f56])).

fof(f56,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f138,f98])).

fof(f98,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v2_funct_1(sK2)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f137,f86])).

fof(f86,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK2)
        | ~ v2_funct_1(sK2)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f52,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v2_funct_1(sK2)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl3_16 ),
    inference(superposition,[],[f39,f133])).

fof(f133,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f161,plain,
    ( ~ spl3_19
    | ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f152,f92,f67,f159])).

fof(f92,plain,
    ( spl3_8
  <=> sK1 = k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f152,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | ~ spl3_5
    | spl3_8 ),
    inference(forward_demodulation,[],[f93,f71])).

fof(f71,plain,
    ( ! [X1] : k8_relset_1(sK0,sK0,sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f93,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f157,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f145,f120,f85,f55,f51,f155])).

fof(f120,plain,
    ( spl3_14
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f145,plain,
    ( sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(resolution,[],[f126,f56])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f125,f86])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK2)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f124,f52])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_14 ),
    inference(superposition,[],[f40,f121])).

fof(f121,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f144,plain,
    ( ~ spl3_17
    | ~ spl3_5
    | spl3_10 ),
    inference(avatar_split_clause,[],[f140,f101,f67,f142])).

fof(f101,plain,
    ( spl3_10
  <=> sK1 = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f140,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ spl3_5
    | spl3_10 ),
    inference(superposition,[],[f102,f71])).

fof(f102,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f135,plain,
    ( spl3_16
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f134,f128,f116,f132])).

fof(f116,plain,
    ( spl3_13
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f128,plain,
    ( spl3_15
  <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f134,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f129,f117])).

fof(f117,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f129,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl3_15
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f75,f67,f128])).

fof(f75,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f122,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f114,f109,f105,f85,f120])).

fof(f105,plain,
    ( spl3_11
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f109,plain,
    ( spl3_12
  <=> v2_funct_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f114,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f113,f86])).

fof(f113,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f112,f106])).

fof(f106,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f110,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f118,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f83,f67,f59,f51,f116])).

fof(f59,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f82,f52])).

fof(f82,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f77,f60])).

fof(f60,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f111,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f81,f67,f63,f51,f109])).

fof(f63,plain,
    ( spl3_4
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f80,f64])).

fof(f64,plain,
    ( v3_funct_2(sK2,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_2(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f74,f52])).

% (2332)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f74,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_2(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f107,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f76,f67,f105])).

fof(f76,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f103,plain,
    ( ~ spl3_10
    | ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f95,f89,f67,f101])).

fof(f89,plain,
    ( spl3_7
  <=> sK1 = k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ spl3_5
    | spl3_7 ),
    inference(forward_demodulation,[],[f90,f70])).

fof(f90,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f99,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f79,f67,f63,f51,f97])).

fof(f79,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f78,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f73,f52])).

fof(f73,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,
    ( ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f31,f92,f89])).

fof(f31,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f87,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f72,f67,f85])).

fof(f72,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f69,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f55])).

fof(f36,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (2340)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (2325)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (2325)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f87,f94,f99,f103,f107,f111,f118,f122,f130,f135,f144,f157,f161,f162,f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~spl3_5 | ~spl3_18 | spl3_19),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    $false | (~spl3_5 | ~spl3_18 | spl3_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl3_18 <=> sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | (~spl3_5 | spl3_19)),
% 0.21/0.50    inference(superposition,[],[f160,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f68,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | spl3_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl3_19 <=> sK1 = k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl3_17 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f146,f132,f97,f85,f55,f51,f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl3_17 <=> sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl3_2 <=> r1_tarski(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl3_6 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl3_9 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl3_16 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_16)),
% 0.21/0.50    inference(resolution,[],[f139,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) ) | (~spl3_1 | ~spl3_6 | ~spl3_9 | ~spl3_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f138,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) ) | (~spl3_1 | ~spl3_6 | ~spl3_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) ) | (~spl3_1 | ~spl3_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f136,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f51])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) ) | ~spl3_16),
% 0.21/0.50    inference(superposition,[],[f39,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~spl3_19 | ~spl3_5 | spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f152,f92,f67,f159])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl3_8 <=> sK1 = k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | (~spl3_5 | spl3_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f93,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X1] : (k8_relset_1(sK0,sK0,sK2,X1) = k10_relat_1(sK2,X1)) ) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f68,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f120,f85,f55,f51,f155])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl3_14 <=> sK0 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_14)),
% 0.21/0.50    inference(resolution,[],[f126,f56])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | (~spl3_1 | ~spl3_6 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f125,f86])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK2) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | (~spl3_1 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f52])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_14),
% 0.21/0.50    inference(superposition,[],[f40,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK2) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~spl3_17 | ~spl3_5 | spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f101,f67,f142])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl3_10 <=> sK1 = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | (~spl3_5 | spl3_10)),
% 0.21/0.50    inference(superposition,[],[f102,f71])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl3_16 | ~spl3_13 | ~spl3_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f128,f116,f132])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl3_13 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl3_15 <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | (~spl3_13 | ~spl3_15)),
% 0.21/0.50    inference(forward_demodulation,[],[f129,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) | ~spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl3_15 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f75,f67,f128])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f68,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl3_14 | ~spl3_6 | ~spl3_11 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f114,f109,f105,f85,f120])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl3_11 <=> v5_relat_1(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl3_12 <=> v2_funct_2(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK2) | (~spl3_6 | ~spl3_11 | ~spl3_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f113,f86])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_11 | ~spl3_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    v5_relat_1(sK2,sK0) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ~v5_relat_1(sK2,sK0) | sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_12),
% 0.21/0.50    inference(resolution,[],[f110,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v2_funct_2(sK2,sK0) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl3_13 | ~spl3_1 | ~spl3_3 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f83,f67,f59,f51,f116])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl3_3 <=> v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK0,sK2) | (~spl3_1 | ~spl3_3 | ~spl3_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f82,f52])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | sK0 = k1_relset_1(sK0,sK0,sK2) | (~spl3_3 | ~spl3_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK0) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f68,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl3_12 | ~spl3_1 | ~spl3_4 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f81,f67,f63,f51,f109])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl3_4 <=> v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    v2_funct_2(sK2,sK0) | (~spl3_1 | ~spl3_4 | ~spl3_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    v3_funct_2(sK2,sK0,sK0) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~v3_funct_2(sK2,sK0,sK0) | v2_funct_2(sK2,sK0) | (~spl3_1 | ~spl3_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f52])).
% 0.21/0.51  % (2332)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | v2_funct_2(sK2,sK0) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f68,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl3_11 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f76,f67,f105])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    v5_relat_1(sK2,sK0) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f68,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~spl3_10 | ~spl3_5 | spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f95,f89,f67,f101])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl3_7 <=> sK1 = k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | (~spl3_5 | spl3_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f90,f70])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl3_9 | ~spl3_1 | ~spl3_4 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f67,f63,f51,f97])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v2_funct_1(sK2) | (~spl3_1 | ~spl3_4 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f64])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~v3_funct_2(sK2,sK0,sK0) | v2_funct_1(sK2) | (~spl3_1 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f52])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | v2_funct_1(sK2) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f68,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~spl3_7 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f92,f89])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl3_6 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f72,f67,f85])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f68,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f67])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f63])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f59])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f55])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f51])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2325)------------------------------
% 0.21/0.51  % (2325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2325)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2325)Memory used [KB]: 6268
% 0.21/0.51  % (2325)Time elapsed: 0.010 s
% 0.21/0.51  % (2325)------------------------------
% 0.21/0.51  % (2325)------------------------------
% 0.21/0.52  % (2339)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.23/0.52  % (2319)Success in time 0.147 s
%------------------------------------------------------------------------------
