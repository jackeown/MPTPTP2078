%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 155 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  265 ( 406 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f52,f56,f60,f64,f72,f76,f80,f86,f91,f103,f109,f123,f129,f140,f146,f151,f289,f292])).

fof(f292,plain,
    ( spl4_1
    | ~ spl4_24
    | ~ spl4_51 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl4_1
    | ~ spl4_24
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f290,f150])).

fof(f150,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_24
  <=> ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f290,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,sK2),sK0)
    | spl4_1
    | ~ spl4_51 ),
    inference(superposition,[],[f37,f288])).

fof(f288,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl4_51
  <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f37,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f289,plain,
    ( spl4_51
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f285,f78,f40,f287])).

fof(f40,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f285,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f79,f42])).

fof(f42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f79,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f151,plain,
    ( spl4_24
    | ~ spl4_22
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f147,f144,f137,f149])).

fof(f137,plain,
    ( spl4_22
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f144,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(sK3,X0),X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f147,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0)
    | ~ spl4_22
    | ~ spl4_23 ),
    inference(resolution,[],[f145,f139])).

fof(f139,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK3),X1)
        | r1_tarski(k10_relat_1(sK3,X0),X1) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl4_23
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f142,f107,f83,f144])).

fof(f83,plain,
    ( spl4_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f107,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | r1_tarski(k10_relat_1(X0,X2),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(sK3,X0),X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) )
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(resolution,[],[f108,f85])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(X0,X2),X1)
        | ~ r1_tarski(k1_relat_1(X0),X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f140,plain,
    ( spl4_22
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f131,f126,f89,f137])).

fof(f89,plain,
    ( spl4_13
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f126,plain,
    ( spl4_20
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f131,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(superposition,[],[f90,f128])).

fof(f128,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f90,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f129,plain,
    ( spl4_20
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f124,f121,f100,f126])).

fof(f100,plain,
    ( spl4_15
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f121,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f124,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(resolution,[],[f122,f102])).

fof(f102,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f119,f83,f58,f121])).

fof(f58,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f59,f85])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f109,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f104,f74,f50,f107])).

fof(f50,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | r1_tarski(k10_relat_1(X0,X2),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f103,plain,
    ( spl4_15
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f98,f70,f40,f100])).

fof(f70,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f98,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f71,f42])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f91,plain,
    ( spl4_13
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f87,f83,f54,f89])).

fof(f54,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f87,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f86,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f81,f62,f40,f83])).

fof(f62,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f81,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f80,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f76,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f72,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f64,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f60,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f56,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f52,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f43,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f38,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f35])).

fof(f25,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (2887)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (2884)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (2885)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (2885)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f293,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f38,f43,f52,f56,f60,f64,f72,f76,f80,f86,f91,f103,f109,f123,f129,f140,f146,f151,f289,f292])).
% 0.21/0.42  fof(f292,plain,(
% 0.21/0.42    spl4_1 | ~spl4_24 | ~spl4_51),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f291])).
% 0.21/0.42  fof(f291,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_24 | ~spl4_51)),
% 0.21/0.42    inference(subsumption_resolution,[],[f290,f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(sK3,X0),sK0)) ) | ~spl4_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f149])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    spl4_24 <=> ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.42  fof(f290,plain,(
% 0.21/0.42    ~r1_tarski(k10_relat_1(sK3,sK2),sK0) | (spl4_1 | ~spl4_51)),
% 0.21/0.42    inference(superposition,[],[f37,f288])).
% 0.21/0.42  fof(f288,plain,(
% 0.21/0.42    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_51),
% 0.21/0.42    inference(avatar_component_clause,[],[f287])).
% 0.21/0.42  fof(f287,plain,(
% 0.21/0.42    spl4_51 <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f289,plain,(
% 0.21/0.42    spl4_51 | ~spl4_2 | ~spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f285,f78,f40,f287])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_11 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f285,plain,(
% 0.21/0.42    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | (~spl4_2 | ~spl4_11)),
% 0.21/0.42    inference(resolution,[],[f79,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    spl4_24 | ~spl4_22 | ~spl4_23),
% 0.21/0.42    inference(avatar_split_clause,[],[f147,f144,f137,f149])).
% 0.21/0.42  fof(f137,plain,(
% 0.21/0.42    spl4_22 <=> r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    spl4_23 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(sK3,X0),X1) | ~r1_tarski(k1_relat_1(sK3),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(sK3,X0),sK0)) ) | (~spl4_22 | ~spl4_23)),
% 0.21/0.42    inference(resolution,[],[f145,f139])).
% 0.21/0.42  fof(f139,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK3),sK0) | ~spl4_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f137])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X1) | r1_tarski(k10_relat_1(sK3,X0),X1)) ) | ~spl4_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f144])).
% 0.21/0.42  fof(f146,plain,(
% 0.21/0.42    spl4_23 | ~spl4_12 | ~spl4_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f142,f107,f83,f144])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl4_12 <=> v1_relat_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl4_16 <=> ! [X1,X0,X2] : (~r1_tarski(k1_relat_1(X0),X1) | r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK3,X0),X1) | ~r1_tarski(k1_relat_1(sK3),X1)) ) | (~spl4_12 | ~spl4_16)),
% 0.21/0.42    inference(resolution,[],[f108,f85])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    v1_relat_1(sK3) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f83])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X2),X1) | ~r1_tarski(k1_relat_1(X0),X1)) ) | ~spl4_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f107])).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    spl4_22 | ~spl4_13 | ~spl4_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f131,f126,f89,f137])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl4_13 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    spl4_20 <=> sK3 = k7_relat_1(sK3,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK3),sK0) | (~spl4_13 | ~spl4_20)),
% 0.21/0.42    inference(superposition,[],[f90,f128])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    sK3 = k7_relat_1(sK3,sK0) | ~spl4_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f126])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    spl4_20 | ~spl4_15 | ~spl4_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f124,f121,f100,f126])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    spl4_15 <=> v4_relat_1(sK3,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    spl4_19 <=> ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    sK3 = k7_relat_1(sK3,sK0) | (~spl4_15 | ~spl4_19)),
% 0.21/0.42    inference(resolution,[],[f122,f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    v4_relat_1(sK3,sK0) | ~spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f100])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) ) | ~spl4_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f121])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    spl4_19 | ~spl4_6 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f119,f83,f58,f121])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl4_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) ) | (~spl4_6 | ~spl4_12)),
% 0.21/0.42    inference(resolution,[],[f59,f85])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    spl4_16 | ~spl4_4 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f104,f74,f50,f107])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl4_4 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_relat_1(X0)) ) | (~spl4_4 | ~spl4_10)),
% 0.21/0.42    inference(resolution,[],[f75,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl4_15 | ~spl4_2 | ~spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f98,f70,f40,f100])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_9 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    v4_relat_1(sK3,sK0) | (~spl4_2 | ~spl4_9)),
% 0.21/0.42    inference(resolution,[],[f71,f42])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl4_13 | ~spl4_5 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f87,f83,f54,f89])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl4_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) ) | (~spl4_5 | ~spl4_12)),
% 0.21/0.42    inference(resolution,[],[f85,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) ) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl4_12 | ~spl4_2 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f81,f62,f40,f83])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    v1_relat_1(sK3) | (~spl4_2 | ~spl4_7)),
% 0.21/0.42    inference(resolution,[],[f63,f42])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f62])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f33,f78])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f32,f74])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f70])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f62])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f54])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f50])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f40])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f35])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2885)------------------------------
% 0.21/0.42  % (2885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2885)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2885)Memory used [KB]: 10746
% 0.21/0.42  % (2885)Time elapsed: 0.010 s
% 0.21/0.42  % (2885)------------------------------
% 0.21/0.42  % (2885)------------------------------
% 0.21/0.42  % (2879)Success in time 0.067 s
%------------------------------------------------------------------------------
