%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 251 expanded)
%              Number of leaves         :   29 ( 101 expanded)
%              Depth                    :    9
%              Number of atoms          :  381 ( 785 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f963,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f73,f77,f89,f93,f107,f114,f121,f126,f131,f172,f183,f185,f193,f213,f224,f232,f378,f389,f962])).

fof(f962,plain,
    ( ~ spl5_1
    | ~ spl5_9
    | spl5_14
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_9
    | spl5_14
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f956,f130])).

fof(f130,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_14
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f956,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_1
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(resolution,[],[f429,f101])).

fof(f101,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f65,f96])).

fof(f96,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f55,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0)
        | r1_tarski(k9_relat_1(sK2,sK3),X0) )
    | ~ spl5_36 ),
    inference(resolution,[],[f377,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f377,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl5_36
  <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f389,plain,
    ( spl5_17
    | ~ spl5_8
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f252,f230,f87,f153])).

fof(f153,plain,
    ( spl5_17
  <=> r1_tarski(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f87,plain,
    ( spl5_8
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f230,plain,
    ( spl5_23
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f252,plain,
    ( r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_8
    | ~ spl5_23 ),
    inference(resolution,[],[f231,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(sK3,X0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f231,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f378,plain,
    ( spl5_36
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f263,f119,f105,f376])).

fof(f105,plain,
    ( spl5_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f119,plain,
    ( spl5_13
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f263,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(resolution,[],[f117,f120])).

fof(f120,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f117,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X2)) )
    | ~ spl5_10 ),
    inference(resolution,[],[f106,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f232,plain,
    ( spl5_23
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f225,f211,f105,f230])).

fof(f211,plain,
    ( spl5_22
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f225,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(superposition,[],[f116,f212])).

fof(f212,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f116,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
    | ~ spl5_10 ),
    inference(resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f224,plain,
    ( spl5_2
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl5_2
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f214,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f214,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_19 ),
    inference(superposition,[],[f59,f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f59,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f213,plain,
    ( spl5_22
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f207,f167,f91,f211])).

fof(f167,plain,
    ( spl5_18
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f207,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(superposition,[],[f168,f99])).

fof(f99,plain,
    ( ! [X1] : k8_relset_1(sK0,sK1,sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f168,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f193,plain,
    ( ~ spl5_17
    | ~ spl5_1
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f191,f129,f119,f105,f54,f153])).

fof(f191,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f190,f182])).

fof(f182,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f190,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f189,f106])).

fof(f189,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f186,f55])).

fof(f186,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_14 ),
    inference(resolution,[],[f184,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f184,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f185,plain,
    ( spl5_14
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f159,f109,f91,f129])).

fof(f109,plain,
    ( spl5_11
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f159,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f110,f97])).

fof(f97,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f110,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f183,plain,
    ( ~ spl5_13
    | ~ spl5_9
    | spl5_12 ),
    inference(avatar_split_clause,[],[f156,f112,f91,f119])).

fof(f112,plain,
    ( spl5_12
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f156,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | spl5_12 ),
    inference(forward_demodulation,[],[f125,f99])).

fof(f125,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f172,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f103,f91,f75,f54,f170,f167])).

fof(f75,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f102,plain,
    ( ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f98,f76])).

fof(f76,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f98,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f131,plain,
    ( ~ spl5_14
    | ~ spl5_9
    | spl5_11 ),
    inference(avatar_split_clause,[],[f127,f109,f91,f129])).

fof(f127,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_9
    | spl5_11 ),
    inference(forward_demodulation,[],[f124,f97])).

fof(f124,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f126,plain,
    ( ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f31,f112,f109])).

fof(f31,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f15])).

% (30241)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(f121,plain,
    ( spl5_13
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f115,f112,f91,f119])).

fof(f115,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f113,f99])).

fof(f113,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( spl5_11
    | spl5_12 ),
    inference(avatar_split_clause,[],[f30,f112,f109])).

fof(f30,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f96,f91,f105])).

fof(f93,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f83,f71,f87])).

fof(f71,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f83,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f77,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f54])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:00:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30226)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (30240)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (30227)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (30230)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (30234)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (30232)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (30244)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (30236)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (30226)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (30231)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f963,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f56,f60,f73,f77,f89,f93,f107,f114,f121,f126,f131,f172,f183,f185,f193,f213,f224,f232,f378,f389,f962])).
% 0.21/0.53  fof(f962,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_9 | spl5_14 | ~spl5_36),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f961])).
% 0.21/0.53  fof(f961,plain,(
% 0.21/0.53    $false | (~spl5_1 | ~spl5_9 | spl5_14 | ~spl5_36)),
% 0.21/0.53    inference(subsumption_resolution,[],[f956,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl5_14 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f956,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_1 | ~spl5_9 | ~spl5_36)),
% 0.21/0.53    inference(resolution,[],[f429,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | (~spl5_1 | ~spl5_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f65,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f92,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | ~spl5_1),
% 0.21/0.53    inference(resolution,[],[f55,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    v1_funct_1(sK2) | ~spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0) | r1_tarski(k9_relat_1(sK2,sK3),X0)) ) | ~spl5_36),
% 0.21/0.53    inference(resolution,[],[f377,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl5_36),
% 0.21/0.53    inference(avatar_component_clause,[],[f376])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    spl5_36 <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    spl5_17 | ~spl5_8 | ~spl5_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f252,f230,f87,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    spl5_17 <=> r1_tarski(sK3,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl5_8 <=> r1_tarski(sK3,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    spl5_23 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_8 | ~spl5_23)),
% 0.21/0.53    inference(resolution,[],[f231,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK3,X0)) ) | ~spl5_8),
% 0.21/0.53    inference(resolution,[],[f88,f42])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    r1_tarski(sK3,sK0) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl5_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f230])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    spl5_36 | ~spl5_10 | ~spl5_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f263,f119,f105,f376])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl5_10 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl5_13 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | (~spl5_10 | ~spl5_13)),
% 0.21/0.53    inference(resolution,[],[f117,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f119])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r1_tarski(X1,X2) | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X2))) ) | ~spl5_10),
% 0.21/0.53    inference(resolution,[],[f106,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    spl5_23 | ~spl5_10 | ~spl5_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f225,f211,f105,f230])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    spl5_22 <=> sK0 = k10_relat_1(sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    r1_tarski(sK0,k1_relat_1(sK2)) | (~spl5_10 | ~spl5_22)),
% 0.21/0.53    inference(superposition,[],[f116,f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    sK0 = k10_relat_1(sK2,sK1) | ~spl5_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f211])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))) ) | ~spl5_10),
% 0.21/0.53    inference(resolution,[],[f106,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    spl5_2 | ~spl5_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    $false | (spl5_2 | ~spl5_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f214,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_19)),
% 0.21/0.53    inference(superposition,[],[f59,f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl5_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl5_19 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1) | spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl5_2 <=> v1_xboole_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    spl5_22 | ~spl5_9 | ~spl5_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f207,f167,f91,f211])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    spl5_18 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    sK0 = k10_relat_1(sK2,sK1) | (~spl5_9 | ~spl5_18)),
% 0.21/0.53    inference(superposition,[],[f168,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X1] : (k8_relset_1(sK0,sK1,sK2,X1) = k10_relat_1(sK2,X1)) ) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f92,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl5_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f167])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~spl5_17 | ~spl5_1 | ~spl5_10 | spl5_13 | ~spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f191,f129,f119,f105,f54,f153])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | ~spl5_10 | spl5_13 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f182])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f119])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k1_relat_1(sK2)) | r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_1 | ~spl5_10 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f106])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_1 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f186,f55])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_14),
% 0.21/0.53    inference(resolution,[],[f184,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    spl5_14 | ~spl5_9 | ~spl5_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f159,f109,f91,f129])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl5_11 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | ~spl5_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f110,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f92,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ~spl5_13 | ~spl5_9 | spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f156,f112,f91,f119])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl5_12 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | spl5_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f125,f99])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f112])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    spl5_18 | spl5_19 | ~spl5_1 | ~spl5_6 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f103,f91,f75,f54,f170,f167])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl5_1 | ~spl5_6 | ~spl5_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f102,f55])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl5_6 | ~spl5_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f75])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f92,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~spl5_14 | ~spl5_9 | spl5_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f127,f109,f91,f129])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | spl5_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f124,f97])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~spl5_11 | ~spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f112,f109])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % (30241)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl5_13 | ~spl5_9 | ~spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f115,f112,f91,f119])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | ~spl5_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f113,f99])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f112])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl5_11 | spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f112,f109])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl5_10 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f96,f91,f105])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f91])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl5_8 | ~spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f83,f71,f87])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    r1_tarski(sK3,sK0) | ~spl5_5),
% 0.21/0.53    inference(resolution,[],[f72,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f71])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f75])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f71])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ~spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f58])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f54])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30226)------------------------------
% 0.21/0.53  % (30226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30226)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30226)Memory used [KB]: 6780
% 0.21/0.53  % (30226)Time elapsed: 0.108 s
% 0.21/0.53  % (30226)------------------------------
% 0.21/0.53  % (30226)------------------------------
% 0.21/0.53  % (30237)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (30225)Success in time 0.17 s
%------------------------------------------------------------------------------
