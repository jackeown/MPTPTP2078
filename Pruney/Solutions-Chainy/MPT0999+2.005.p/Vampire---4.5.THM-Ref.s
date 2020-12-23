%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 148 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 372 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f48,f52,f56,f64,f68,f72,f76,f80,f87,f92,f105,f115,f120,f175,f181,f193,f198])).

fof(f198,plain,
    ( ~ spl4_7
    | ~ spl4_12
    | ~ spl4_15
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_15
    | spl4_31 ),
    inference(subsumption_resolution,[],[f196,f86])).

fof(f86,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f196,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_15
    | spl4_31 ),
    inference(subsumption_resolution,[],[f194,f104])).

fof(f104,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_15
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f194,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_7
    | spl4_31 ),
    inference(resolution,[],[f192,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f192,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl4_31
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f193,plain,
    ( ~ spl4_31
    | ~ spl4_18
    | spl4_29 ),
    inference(avatar_split_clause,[],[f183,f178,f118,f190])).

fof(f118,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X1)
        | r1_tarski(k10_relat_1(sK3,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f178,plain,
    ( spl4_29
  <=> r1_tarski(k10_relat_1(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f183,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_18
    | spl4_29 ),
    inference(resolution,[],[f180,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(sK3,X0),X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f180,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,sK2),sK0)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( ~ spl4_29
    | spl4_1
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f176,f173,f36,f178])).

fof(f36,plain,
    ( spl4_1
  <=> r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f173,plain,
    ( spl4_28
  <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f176,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,sK2),sK0)
    | spl4_1
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f38,f174])).

fof(f174,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f173])).

fof(f38,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f175,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f171,f78,f41,f173])).

fof(f41,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f171,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f79,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f120,plain,
    ( spl4_18
    | ~ spl4_9
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f116,f113,f70,f118])).

fof(f70,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f113,plain,
    ( spl4_17
  <=> ! [X3] : k1_relat_1(sK3) = k2_xboole_0(k10_relat_1(sK3,X3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

% (21319)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK3),X1)
        | r1_tarski(k10_relat_1(sK3,X0),X1) )
    | ~ spl4_9
    | ~ spl4_17 ),
    inference(superposition,[],[f71,f114])).

fof(f114,plain,
    ( ! [X3] : k1_relat_1(sK3) = k2_xboole_0(k10_relat_1(sK3,X3),k1_relat_1(sK3))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f115,plain,
    ( spl4_17
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f107,f90,f84,f113])).

fof(f90,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f107,plain,
    ( ! [X3] : k1_relat_1(sK3) = k2_xboole_0(k10_relat_1(sK3,X3),k1_relat_1(sK3))
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(resolution,[],[f91,f86])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f105,plain,
    ( spl4_15
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f100,f74,f41,f102])).

fof(f74,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f100,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f75,f43])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f92,plain,
    ( spl4_13
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f88,f66,f54,f90])).

fof(f54,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f66,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f87,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f82,f50,f46,f41,f84])).

fof(f46,plain,
    ( spl4_3
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f50,plain,
    ( spl4_4
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f82,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f81,f51])).

fof(f51,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f81,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f80,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f76,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f72,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f68,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f64,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f56,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f52,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f48,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f36])).

fof(f25,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:51:24 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.41  % (21326)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (21329)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (21323)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  % (21329)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f199,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f39,f44,f48,f52,f56,f64,f68,f72,f76,f80,f87,f92,f105,f115,f120,f175,f181,f193,f198])).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    ~spl4_7 | ~spl4_12 | ~spl4_15 | spl4_31),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    $false | (~spl4_7 | ~spl4_12 | ~spl4_15 | spl4_31)),
% 0.20/0.43    inference(subsumption_resolution,[],[f196,f86])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl4_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f84])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl4_12 <=> v1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f196,plain,(
% 0.20/0.43    ~v1_relat_1(sK3) | (~spl4_7 | ~spl4_15 | spl4_31)),
% 0.20/0.43    inference(subsumption_resolution,[],[f194,f104])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    v4_relat_1(sK3,sK0) | ~spl4_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f102])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl4_15 <=> v4_relat_1(sK3,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.43  fof(f194,plain,(
% 0.20/0.43    ~v4_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | (~spl4_7 | spl4_31)),
% 0.20/0.43    inference(resolution,[],[f192,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl4_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl4_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.43  fof(f192,plain,(
% 0.20/0.43    ~r1_tarski(k1_relat_1(sK3),sK0) | spl4_31),
% 0.20/0.43    inference(avatar_component_clause,[],[f190])).
% 0.20/0.43  fof(f190,plain,(
% 0.20/0.43    spl4_31 <=> r1_tarski(k1_relat_1(sK3),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.43  fof(f193,plain,(
% 0.20/0.43    ~spl4_31 | ~spl4_18 | spl4_29),
% 0.20/0.43    inference(avatar_split_clause,[],[f183,f178,f118,f190])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    spl4_18 <=> ! [X1,X0] : (~r1_tarski(k1_relat_1(sK3),X1) | r1_tarski(k10_relat_1(sK3,X0),X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.43  fof(f178,plain,(
% 0.20/0.43    spl4_29 <=> r1_tarski(k10_relat_1(sK3,sK2),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    ~r1_tarski(k1_relat_1(sK3),sK0) | (~spl4_18 | spl4_29)),
% 0.20/0.43    inference(resolution,[],[f180,f119])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK3,X0),X1) | ~r1_tarski(k1_relat_1(sK3),X1)) ) | ~spl4_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f118])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    ~r1_tarski(k10_relat_1(sK3,sK2),sK0) | spl4_29),
% 0.20/0.43    inference(avatar_component_clause,[],[f178])).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    ~spl4_29 | spl4_1 | ~spl4_28),
% 0.20/0.43    inference(avatar_split_clause,[],[f176,f173,f36,f178])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl4_1 <=> r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    spl4_28 <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    ~r1_tarski(k10_relat_1(sK3,sK2),sK0) | (spl4_1 | ~spl4_28)),
% 0.20/0.43    inference(backward_demodulation,[],[f38,f174])).
% 0.20/0.43  fof(f174,plain,(
% 0.20/0.43    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f173])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f36])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    spl4_28 | ~spl4_2 | ~spl4_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f171,f78,f41,f173])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl4_11 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | (~spl4_2 | ~spl4_11)),
% 0.20/0.43    inference(resolution,[],[f79,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f41])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl4_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    spl4_18 | ~spl4_9 | ~spl4_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f116,f113,f70,f118])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    spl4_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    spl4_17 <=> ! [X3] : k1_relat_1(sK3) = k2_xboole_0(k10_relat_1(sK3,X3),k1_relat_1(sK3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.43  % (21319)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X1) | r1_tarski(k10_relat_1(sK3,X0),X1)) ) | (~spl4_9 | ~spl4_17)),
% 0.20/0.43    inference(superposition,[],[f71,f114])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X3] : (k1_relat_1(sK3) = k2_xboole_0(k10_relat_1(sK3,X3),k1_relat_1(sK3))) ) | ~spl4_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f113])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f70])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl4_17 | ~spl4_12 | ~spl4_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f107,f90,f84,f113])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    spl4_13 <=> ! [X1,X0] : (k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    ( ! [X3] : (k1_relat_1(sK3) = k2_xboole_0(k10_relat_1(sK3,X3),k1_relat_1(sK3))) ) | (~spl4_12 | ~spl4_13)),
% 0.20/0.43    inference(resolution,[],[f91,f86])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))) ) | ~spl4_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f90])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    spl4_15 | ~spl4_2 | ~spl4_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f100,f74,f41,f102])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl4_10 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    v4_relat_1(sK3,sK0) | (~spl4_2 | ~spl4_10)),
% 0.20/0.43    inference(resolution,[],[f75,f43])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f74])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl4_13 | ~spl4_5 | ~spl4_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f88,f66,f54,f90])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl4_5 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl4_8 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl4_5 | ~spl4_8)),
% 0.20/0.43    inference(resolution,[],[f67,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f54])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f66])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl4_12 | ~spl4_2 | ~spl4_3 | ~spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f82,f50,f46,f41,f84])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl4_3 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl4_4 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    v1_relat_1(sK3) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f81,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl4_2 | ~spl4_3)),
% 0.20/0.43    inference(resolution,[],[f47,f43])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f46])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl4_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f78])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    spl4_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f74])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f70])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl4_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f66])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl4_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f62])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f54])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f50])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f46])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f41])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.43  fof(f10,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.20/0.43    inference(negated_conjecture,[],[f9])).
% 0.20/0.43  fof(f9,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f36])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (21329)------------------------------
% 0.20/0.43  % (21329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (21329)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (21329)Memory used [KB]: 6140
% 0.20/0.43  % (21329)Time elapsed: 0.005 s
% 0.20/0.43  % (21329)------------------------------
% 0.20/0.43  % (21329)------------------------------
% 0.20/0.44  % (21327)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (21318)Success in time 0.084 s
%------------------------------------------------------------------------------
