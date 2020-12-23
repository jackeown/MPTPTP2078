%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 124 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :  205 ( 311 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f39,f43,f47,f51,f55,f59,f64,f70,f80,f86,f92,f197,f232,f258])).

fof(f258,plain,
    ( spl4_13
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl4_13
    | ~ spl4_41 ),
    inference(resolution,[],[f231,f85])).

fof(f85,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_13
  <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f231,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl4_41
  <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f232,plain,
    ( spl4_41
    | ~ spl4_10
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f228,f195,f90,f67,f230])).

fof(f67,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f90,plain,
    ( spl4_14
  <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f195,plain,
    ( spl4_35
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f228,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ spl4_10
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f223,f69])).

fof(f69,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f223,plain,
    ( ! [X0] :
        ( m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(resolution,[],[f196,f91])).

fof(f91,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f196,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_relat_1(X1) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl4_35
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f193,f57,f45,f195])).

fof(f45,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r1_tarski(k2_relat_1(X3),X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f193,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_relat_1(X1) )
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f58,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relat_1(X3),X1)
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f92,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f88,f78,f53,f32,f90])).

fof(f32,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f78,plain,
    ( spl4_12
  <=> ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f87,f79])).

fof(f79,plain,
    ( ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f87,plain,
    ( ! [X0] : m1_subset_1(k6_relset_1(sK2,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f86,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f81,f78,f27,f83])).

fof(f27,plain,
    ( spl4_1
  <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f29,f79])).

fof(f29,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f80,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f76,f49,f32,f78])).

fof(f49,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] :
        ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f50,f34])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f65,f62,f32,f67])).

fof(f62,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f65,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f63,f34])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f60,f41,f37,f62])).

fof(f37,plain,
    ( spl4_3
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f41,plain,
    ( spl4_4
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f59,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f55,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

fof(f51,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f47,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f43,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f35,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

fof(f30,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f27])).

fof(f19,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (25444)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (25444)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f259,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f30,f35,f39,f43,f47,f51,f55,f59,f64,f70,f80,f86,f92,f197,f232,f258])).
% 0.21/0.42  fof(f258,plain,(
% 0.21/0.42    spl4_13 | ~spl4_41),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f253])).
% 0.21/0.42  fof(f253,plain,(
% 0.21/0.42    $false | (spl4_13 | ~spl4_41)),
% 0.21/0.42    inference(resolution,[],[f231,f85])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f83])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl4_13 <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f231,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl4_41),
% 0.21/0.42    inference(avatar_component_clause,[],[f230])).
% 0.21/0.42  fof(f230,plain,(
% 0.21/0.42    spl4_41 <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.42  fof(f232,plain,(
% 0.21/0.42    spl4_41 | ~spl4_10 | ~spl4_14 | ~spl4_35),
% 0.21/0.42    inference(avatar_split_clause,[],[f228,f195,f90,f67,f230])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl4_10 <=> v1_relat_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl4_14 <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    spl4_35 <=> ! [X1,X3,X0,X2] : (m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.42  fof(f228,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | (~spl4_10 | ~spl4_14 | ~spl4_35)),
% 0.21/0.42    inference(subsumption_resolution,[],[f223,f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    v1_relat_1(sK3) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f67])).
% 0.21/0.42  fof(f223,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_relat_1(sK3)) ) | (~spl4_14 | ~spl4_35)),
% 0.21/0.42    inference(resolution,[],[f196,f91])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f90])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(X1)) ) | ~spl4_35),
% 0.21/0.42    inference(avatar_component_clause,[],[f195])).
% 0.21/0.42  fof(f197,plain,(
% 0.21/0.42    spl4_35 | ~spl4_5 | ~spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f193,f57,f45,f195])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl4_5 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl4_8 <=> ! [X1,X3,X0,X2] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f193,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_relat_1(X1)) ) | (~spl4_5 | ~spl4_8)),
% 0.21/0.42    inference(resolution,[],[f58,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    spl4_14 | ~spl4_2 | ~spl4_7 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f88,f78,f53,f32,f90])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X3,X0,X2] : (m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_12 <=> ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_2 | ~spl4_7 | ~spl4_12)),
% 0.21/0.42    inference(forward_demodulation,[],[f87,f79])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)) ) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k6_relset_1(sK2,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_2 | ~spl4_7)),
% 0.21/0.42    inference(resolution,[],[f54,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ~spl4_13 | spl4_1 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f81,f78,f27,f83])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl4_1 <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_1 | ~spl4_12)),
% 0.21/0.42    inference(superposition,[],[f29,f79])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl4_12 | ~spl4_2 | ~spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f76,f49,f32,f78])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl4_6 <=> ! [X1,X3,X0,X2] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)) ) | (~spl4_2 | ~spl4_6)),
% 0.21/0.42    inference(resolution,[],[f50,f34])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_10 | ~spl4_2 | ~spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f65,f62,f32,f67])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl4_9 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    v1_relat_1(sK3) | (~spl4_2 | ~spl4_9)),
% 0.21/0.42    inference(resolution,[],[f63,f34])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | ~spl4_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f62])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl4_9 | ~spl4_3 | ~spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f60,f41,f37,f62])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl4_3 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl4_4 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | (~spl4_3 | ~spl4_4)),
% 0.21/0.42    inference(resolution,[],[f38,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) ) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f57])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.42    inference(flattening,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f45])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f37])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f27])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (25444)------------------------------
% 0.21/0.43  % (25444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (25444)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (25444)Memory used [KB]: 10746
% 0.21/0.43  % (25444)Time elapsed: 0.010 s
% 0.21/0.43  % (25444)------------------------------
% 0.21/0.43  % (25444)------------------------------
% 0.21/0.43  % (25441)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (25436)Success in time 0.072 s
%------------------------------------------------------------------------------
