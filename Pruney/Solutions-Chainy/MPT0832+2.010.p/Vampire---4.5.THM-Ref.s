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
% DateTime   : Thu Dec  3 12:57:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 142 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :  221 ( 337 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f72,f80,f85,f90,f96,f102,f212,f309,f321,f332])).

fof(f332,plain,
    ( spl4_14
    | ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl4_14
    | ~ spl4_57 ),
    inference(resolution,[],[f320,f95])).

fof(f95,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_14
  <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f320,plain,
    ( ! [X1] : m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl4_57
  <=> ! [X1] : m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f321,plain,
    ( spl4_57
    | ~ spl4_10
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f311,f307,f69,f319])).

fof(f69,plain,
    ( spl4_10
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f307,plain,
    ( spl4_55
  <=> ! [X1,X0] :
        ( m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f311,plain,
    ( ! [X1] : m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ spl4_10
    | ~ spl4_55 ),
    inference(resolution,[],[f308,f70])).

fof(f70,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1)
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f307])).

fof(f309,plain,
    ( spl4_55
    | ~ spl4_15
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f305,f210,f100,f307])).

fof(f100,plain,
    ( spl4_15
  <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f210,plain,
    ( spl4_36
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1)
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1) )
    | ~ spl4_15
    | ~ spl4_36 ),
    inference(resolution,[],[f211,f101])).

fof(f101,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f211,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( spl4_36
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f207,f83,f63,f210])).

fof(f63,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r1_tarski(k2_relat_1(X3),X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f83,plain,
    ( spl4_12
  <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK3)) = k3_xboole_0(k2_relat_1(sK3),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f207,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1)
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f64,f84])).

fof(f84,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK3)) = k3_xboole_0(k2_relat_1(sK3),X0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relat_1(X3),X1)
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f102,plain,
    ( spl4_15
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f98,f88,f59,f34,f100])).

fof(f34,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f88,plain,
    ( spl4_13
  <=> ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f98,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f97,f89])).

fof(f89,plain,
    ( ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f97,plain,
    ( ! [X0] : m1_subset_1(k6_relset_1(sK2,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f60,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f96,plain,
    ( ~ spl4_14
    | spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f91,f88,f29,f93])).

fof(f29,plain,
    ( spl4_1
  <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1
    | ~ spl4_13 ),
    inference(superposition,[],[f31,f89])).

fof(f31,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f90,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f86,f55,f34,f88])).

fof(f55,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] :
        ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f86,plain,
    ( ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f85,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f81,f77,f47,f83])).

fof(f47,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f77,plain,
    ( spl4_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f81,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK3)) = k3_xboole_0(k2_relat_1(sK3),X0)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f48,f79])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f80,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f75,f51,f34,f77])).

fof(f51,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f75,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f72,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f67,f43,f39,f69])).

fof(f39,plain,
    ( spl4_3
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f43,plain,
    ( spl4_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f40,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f40,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f65,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f61,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

fof(f57,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f53,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f45,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f41,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.42  % (28002)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (28001)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (28005)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (28002)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f333,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f72,f80,f85,f90,f96,f102,f212,f309,f321,f332])).
% 0.22/0.43  fof(f332,plain,(
% 0.22/0.43    spl4_14 | ~spl4_57),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f327])).
% 0.22/0.43  fof(f327,plain,(
% 0.22/0.43    $false | (spl4_14 | ~spl4_57)),
% 0.22/0.43    inference(resolution,[],[f320,f95])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f93])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    spl4_14 <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.43  fof(f320,plain,(
% 0.22/0.43    ( ! [X1] : (m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | ~spl4_57),
% 0.22/0.43    inference(avatar_component_clause,[],[f319])).
% 0.22/0.43  fof(f319,plain,(
% 0.22/0.43    spl4_57 <=> ! [X1] : m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.22/0.43  fof(f321,plain,(
% 0.22/0.43    spl4_57 | ~spl4_10 | ~spl4_55),
% 0.22/0.43    inference(avatar_split_clause,[],[f311,f307,f69,f319])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl4_10 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.43  fof(f307,plain,(
% 0.22/0.43    spl4_55 <=> ! [X1,X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.22/0.43  fof(f311,plain,(
% 0.22/0.43    ( ! [X1] : (m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | (~spl4_10 | ~spl4_55)),
% 0.22/0.43    inference(resolution,[],[f308,f70])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl4_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f69])).
% 0.22/0.43  fof(f308,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | ~spl4_55),
% 0.22/0.43    inference(avatar_component_clause,[],[f307])).
% 0.22/0.43  fof(f309,plain,(
% 0.22/0.43    spl4_55 | ~spl4_15 | ~spl4_36),
% 0.22/0.43    inference(avatar_split_clause,[],[f305,f210,f100,f307])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    spl4_15 <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.43  fof(f210,plain,(
% 0.22/0.43    spl4_36 <=> ! [X1,X3,X0,X2] : (~r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.43  fof(f305,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1)) ) | (~spl4_15 | ~spl4_36)),
% 0.22/0.43    inference(resolution,[],[f211,f101])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f100])).
% 0.22/0.43  fof(f211,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1)) ) | ~spl4_36),
% 0.22/0.43    inference(avatar_component_clause,[],[f210])).
% 0.22/0.43  fof(f212,plain,(
% 0.22/0.43    spl4_36 | ~spl4_9 | ~spl4_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f207,f83,f63,f210])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl4_9 <=> ! [X1,X3,X0,X2] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    spl4_12 <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK3)) = k3_xboole_0(k2_relat_1(sK3),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.43  fof(f207,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~r1_tarski(k3_xboole_0(k2_relat_1(sK3),X0),X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | (~spl4_9 | ~spl4_12)),
% 0.22/0.43    inference(superposition,[],[f64,f84])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK3)) = k3_xboole_0(k2_relat_1(sK3),X0)) ) | ~spl4_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f83])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) ) | ~spl4_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    spl4_15 | ~spl4_2 | ~spl4_8 | ~spl4_13),
% 0.22/0.43    inference(avatar_split_clause,[],[f98,f88,f59,f34,f100])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl4_8 <=> ! [X1,X3,X0,X2] : (m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    spl4_13 <=> ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_2 | ~spl4_8 | ~spl4_13)),
% 0.22/0.43    inference(forward_demodulation,[],[f97,f89])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)) ) | ~spl4_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f88])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k6_relset_1(sK2,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_2 | ~spl4_8)),
% 0.22/0.43    inference(resolution,[],[f60,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f59])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    ~spl4_14 | spl4_1 | ~spl4_13),
% 0.22/0.43    inference(avatar_split_clause,[],[f91,f88,f29,f93])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl4_1 <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_1 | ~spl4_13)),
% 0.22/0.43    inference(superposition,[],[f31,f89])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    spl4_13 | ~spl4_2 | ~spl4_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f86,f55,f34,f88])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    spl4_7 <=> ! [X1,X3,X0,X2] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)) ) | (~spl4_2 | ~spl4_7)),
% 0.22/0.43    inference(resolution,[],[f56,f36])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) ) | ~spl4_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f55])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    spl4_12 | ~spl4_5 | ~spl4_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f81,f77,f47,f83])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl4_5 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl4_11 <=> v1_relat_1(sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK3)) = k3_xboole_0(k2_relat_1(sK3),X0)) ) | (~spl4_5 | ~spl4_11)),
% 0.22/0.43    inference(resolution,[],[f48,f79])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    v1_relat_1(sK3) | ~spl4_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f77])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) ) | ~spl4_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f47])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    spl4_11 | ~spl4_2 | ~spl4_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f75,f51,f34,f77])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl4_6 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    v1_relat_1(sK3) | (~spl4_2 | ~spl4_6)),
% 0.22/0.43    inference(resolution,[],[f52,f36])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f51])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    spl4_10 | ~spl4_3 | ~spl4_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f67,f43,f39,f69])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl4_3 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl4_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.43    inference(superposition,[],[f40,f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f43])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl4_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl4_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl4_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f59])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl4_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f55])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl4_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f51])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    spl4_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f47])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl4_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f43])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl4_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f39])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl4_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.43    inference(negated_conjecture,[],[f8])).
% 0.22/0.43  fof(f8,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ~spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f29])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (28002)------------------------------
% 0.22/0.43  % (28002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (28002)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (28002)Memory used [KB]: 10746
% 0.22/0.43  % (28002)Time elapsed: 0.010 s
% 0.22/0.43  % (28002)------------------------------
% 0.22/0.43  % (28002)------------------------------
% 0.22/0.43  % (27996)Success in time 0.077 s
%------------------------------------------------------------------------------
