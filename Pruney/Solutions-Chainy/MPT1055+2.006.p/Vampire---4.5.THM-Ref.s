%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 226 expanded)
%              Number of leaves         :   28 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  380 ( 738 expanded)
%              Number of equality atoms :   45 (  59 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f581,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f81,f85,f97,f101,f116,f123,f129,f134,f139,f154,f181,f187,f203,f281,f335,f337,f348,f580])).

fof(f580,plain,
    ( ~ spl5_1
    | ~ spl5_9
    | spl5_14
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_9
    | spl5_14
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f577,f138])).

fof(f138,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_14
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f577,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_1
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(resolution,[],[f319,f112])).

fof(f112,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f73,f107])).

fof(f107,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f100,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0)
        | r1_tarski(k9_relat_1(sK2,sK3),X0) )
    | ~ spl5_28 ),
    inference(resolution,[],[f280,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f280,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl5_28
  <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f348,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f346,f96])).

fof(f96,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_8
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f346,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl5_1
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f345,f184])).

fof(f184,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f345,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f344,f334])).

fof(f334,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_13
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f344,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f343,f115])).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f343,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f338,f63])).

fof(f338,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_14 ),
    inference(resolution,[],[f336,f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f336,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f337,plain,
    ( spl5_14
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f285,f118,f99,f137])).

fof(f118,plain,
    ( spl5_11
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f285,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f119,f108])).

fof(f108,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl5_9 ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f119,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f335,plain,
    ( ~ spl5_13
    | ~ spl5_9
    | spl5_12 ),
    inference(avatar_split_clause,[],[f282,f121,f99,f127])).

% (11814)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f121,plain,
    ( spl5_12
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f282,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | spl5_12 ),
    inference(forward_demodulation,[],[f133,f109])).

fof(f109,plain,
    ( ! [X1] : k8_relset_1(sK0,sK1,sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl5_9 ),
    inference(resolution,[],[f100,f39])).

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

fof(f133,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f281,plain,
    ( spl5_28
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f209,f127,f114,f279])).

fof(f209,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(resolution,[],[f125,f128])).

fof(f128,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl5_10 ),
    inference(resolution,[],[f115,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f203,plain,
    ( spl5_2
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl5_2
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f191,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_19 ),
    inference(superposition,[],[f67,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f187,plain,
    ( spl5_20
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f185,f176,f152,f183])).

fof(f152,plain,
    ( spl5_17
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f176,plain,
    ( spl5_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(superposition,[],[f177,f153])).

fof(f153,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f177,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f181,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f111,f99,f83,f179,f176])).

fof(f83,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f106,f84])).

fof(f84,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f100,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f154,plain,
    ( spl5_17
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f104,f99,f152])).

fof(f104,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f100,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f139,plain,
    ( ~ spl5_14
    | ~ spl5_9
    | spl5_11 ),
    inference(avatar_split_clause,[],[f135,f118,f99,f137])).

fof(f135,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_9
    | spl5_11 ),
    inference(forward_demodulation,[],[f132,f108])).

fof(f132,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f134,plain,
    ( ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f31,f121,f118])).

fof(f31,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f129,plain,
    ( spl5_13
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f124,f121,f99,f127])).

fof(f124,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f122,f109])).

fof(f122,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl5_11
    | spl5_12 ),
    inference(avatar_split_clause,[],[f30,f121,f118])).

fof(f30,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f107,f99,f114])).

fof(f101,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f36,f99])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f91,f79,f95])).

fof(f79,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f91,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f85,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.20/0.35  % Computer   : n022.cluster.edu
% 0.20/0.35  % Model      : x86_64 x86_64
% 0.20/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.20/0.35  % Memory     : 8042.1875MB
% 0.20/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 10:57:41 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.43  % (11819)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (11815)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (11823)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (11806)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (11812)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (11808)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (11824)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (11816)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (11807)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11809)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11822)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (11811)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (11810)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (11818)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11820)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (11806)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f581,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f64,f68,f81,f85,f97,f101,f116,f123,f129,f134,f139,f154,f181,f187,f203,f281,f335,f337,f348,f580])).
% 0.21/0.52  fof(f580,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_9 | spl5_14 | ~spl5_28),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f579])).
% 0.21/0.52  fof(f579,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_9 | spl5_14 | ~spl5_28)),
% 0.21/0.52    inference(subsumption_resolution,[],[f577,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl5_14 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f577,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_1 | ~spl5_9 | ~spl5_28)),
% 0.21/0.52    inference(resolution,[],[f319,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | (~spl5_1 | ~spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f100,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | ~spl5_1),
% 0.21/0.52    inference(resolution,[],[f63,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0) | r1_tarski(k9_relat_1(sK2,sK3),X0)) ) | ~spl5_28),
% 0.21/0.52    inference(resolution,[],[f280,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl5_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f279])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    spl5_28 <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_8 | ~spl5_10 | spl5_13 | ~spl5_14 | ~spl5_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f347])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_8 | ~spl5_10 | spl5_13 | ~spl5_14 | ~spl5_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f346,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    r1_tarski(sK3,sK0) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl5_8 <=> r1_tarski(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ~r1_tarski(sK3,sK0) | (~spl5_1 | ~spl5_10 | spl5_13 | ~spl5_14 | ~spl5_20)),
% 0.21/0.52    inference(forward_demodulation,[],[f345,f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2) | ~spl5_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl5_20 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | ~spl5_10 | spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f344,f334])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl5_13 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_relat_1(sK2)) | r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_1 | ~spl5_10 | ~spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f343,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl5_10 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_1 | ~spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f338,f63])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_14),
% 0.21/0.52    inference(resolution,[],[f336,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    spl5_14 | ~spl5_9 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f285,f118,f99,f137])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl5_11 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | ~spl5_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f119,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f100,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    ~spl5_13 | ~spl5_9 | spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f282,f121,f99,f127])).
% 0.21/0.52  % (11814)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl5_12 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | spl5_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f133,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X1] : (k8_relset_1(sK0,sK1,sK2,X1) = k10_relat_1(sK2,X1)) ) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f100,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    spl5_28 | ~spl5_10 | ~spl5_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f209,f127,f114,f279])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | (~spl5_10 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f125,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl5_10),
% 0.21/0.53    inference(resolution,[],[f115,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    spl5_2 | ~spl5_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f202])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    $false | (spl5_2 | ~spl5_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_19)),
% 0.21/0.53    inference(superposition,[],[f67,f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl5_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    spl5_19 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1) | spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl5_2 <=> v1_xboole_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    spl5_20 | ~spl5_17 | ~spl5_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f185,f176,f152,f183])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl5_17 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    spl5_18 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2) | (~spl5_17 | ~spl5_18)),
% 0.21/0.53    inference(superposition,[],[f177,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f176])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl5_18 | spl5_19 | ~spl5_6 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f111,f99,f83,f179,f176])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_6 | ~spl5_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f100,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl5_17 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f104,f99,f152])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f100,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~spl5_14 | ~spl5_9 | spl5_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f135,f118,f99,f137])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | spl5_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f132,f108])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~spl5_11 | ~spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f121,f118])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
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
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl5_13 | ~spl5_9 | ~spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f124,f121,f99,f127])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | ~spl5_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f122,f109])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl5_11 | spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f121,f118])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl5_10 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f107,f99,f114])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f99])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl5_8 | ~spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f91,f79,f95])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    r1_tarski(sK3,sK0) | ~spl5_5),
% 0.21/0.53    inference(resolution,[],[f80,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f79])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f83])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f79])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ~spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f66])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f62])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11806)------------------------------
% 0.21/0.53  % (11806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11806)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11806)Memory used [KB]: 6652
% 0.21/0.53  % (11806)Time elapsed: 0.072 s
% 0.21/0.53  % (11806)------------------------------
% 0.21/0.53  % (11806)------------------------------
% 0.21/0.53  % (11825)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (11805)Success in time 0.164 s
%------------------------------------------------------------------------------
