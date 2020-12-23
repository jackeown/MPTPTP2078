%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 165 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 417 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f66,f91,f100,f107,f122,f127,f131,f152,f158,f171])).

fof(f171,plain,
    ( ~ spl3_2
    | spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl3_2
    | spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f169,f151])).

fof(f151,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_9
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f169,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_2
    | spl3_7
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f121,f167])).

fof(f167,plain,
    ( sK2 = k8_relat_1(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f65,f157,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f157,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_10
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f121,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_7
  <=> r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f158,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f135,f104,f63,f155])).

fof(f104,plain,
    ( spl3_6
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f135,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f65,f106,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f106,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f152,plain,
    ( spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f83,f54,f149])).

fof(f54,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f131,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8 ),
    inference(subsumption_resolution,[],[f129,f83])).

fof(f129,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8 ),
    inference(backward_demodulation,[],[f126,f128])).

fof(f128,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f65,f90,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f90,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_3
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( ~ spl3_8
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f117,f93,f63,f54,f124])).

fof(f93,plain,
    ( spl3_4
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f117,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(backward_demodulation,[],[f95,f116])).

fof(f116,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f109,f80])).

fof(f80,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_partfun1(X0),sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f65,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f34,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f109,plain,
    ( ! [X0] : k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f36,f56,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f95,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f122,plain,
    ( ~ spl3_7
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f115,f97,f63,f54,f119])).

fof(f97,plain,
    ( spl3_5
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(backward_demodulation,[],[f99,f114])).

fof(f114,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f110,f78])).

fof(f78,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_partfun1(X0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f110,plain,
    ( ! [X0] : k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f36,f48])).

fof(f99,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f107,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f71,f54,f104])).

fof(f71,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f100,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f33,f97,f93])).

fof(f33,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f91,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f67,f54,f88])).

fof(f67,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f58,f54,f63])).

fof(f58,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:17:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.45  % (20462)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.18/0.46  % (20462)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % (20454)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.18/0.46  % (20454)Refutation not found, incomplete strategy% (20454)------------------------------
% 0.18/0.46  % (20454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (20454)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (20454)Memory used [KB]: 10618
% 0.18/0.46  % (20454)Time elapsed: 0.070 s
% 0.18/0.46  % (20454)------------------------------
% 0.18/0.46  % (20454)------------------------------
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f172,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(avatar_sat_refutation,[],[f57,f66,f91,f100,f107,f122,f127,f131,f152,f158,f171])).
% 0.18/0.46  fof(f171,plain,(
% 0.18/0.46    ~spl3_2 | spl3_7 | ~spl3_9 | ~spl3_10),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f170])).
% 0.18/0.46  fof(f170,plain,(
% 0.18/0.46    $false | (~spl3_2 | spl3_7 | ~spl3_9 | ~spl3_10)),
% 0.18/0.46    inference(subsumption_resolution,[],[f169,f151])).
% 0.18/0.46  fof(f151,plain,(
% 0.18/0.46    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_9),
% 0.18/0.46    inference(avatar_component_clause,[],[f149])).
% 0.18/0.46  fof(f149,plain,(
% 0.18/0.46    spl3_9 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.18/0.46  fof(f169,plain,(
% 0.18/0.46    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl3_2 | spl3_7 | ~spl3_10)),
% 0.18/0.46    inference(backward_demodulation,[],[f121,f167])).
% 0.18/0.46  fof(f167,plain,(
% 0.18/0.46    sK2 = k8_relat_1(sK1,sK2) | (~spl3_2 | ~spl3_10)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f65,f157,f39])).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.18/0.46    inference(flattening,[],[f17])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.18/0.46  fof(f157,plain,(
% 0.18/0.46    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_10),
% 0.18/0.46    inference(avatar_component_clause,[],[f155])).
% 0.18/0.46  fof(f155,plain,(
% 0.18/0.46    spl3_10 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.18/0.46  fof(f65,plain,(
% 0.18/0.46    v1_relat_1(sK2) | ~spl3_2),
% 0.18/0.46    inference(avatar_component_clause,[],[f63])).
% 0.18/0.46  fof(f63,plain,(
% 0.18/0.46    spl3_2 <=> v1_relat_1(sK2)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.46  fof(f121,plain,(
% 0.18/0.46    ~r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) | spl3_7),
% 0.18/0.46    inference(avatar_component_clause,[],[f119])).
% 0.18/0.46  fof(f119,plain,(
% 0.18/0.46    spl3_7 <=> r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.18/0.47  fof(f158,plain,(
% 0.18/0.47    spl3_10 | ~spl3_2 | ~spl3_6),
% 0.18/0.47    inference(avatar_split_clause,[],[f135,f104,f63,f155])).
% 0.18/0.47  fof(f104,plain,(
% 0.18/0.47    spl3_6 <=> v5_relat_1(sK2,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.47  fof(f135,plain,(
% 0.18/0.47    r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_2 | ~spl3_6)),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f65,f106,f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(nnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.18/0.47  fof(f106,plain,(
% 0.18/0.47    v5_relat_1(sK2,sK1) | ~spl3_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f104])).
% 0.18/0.47  fof(f152,plain,(
% 0.18/0.47    spl3_9 | ~spl3_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f83,f54,f149])).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.47  fof(f83,plain,(
% 0.18/0.47    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_1),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f56,f52])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.18/0.47    inference(duplicate_literal_removal,[],[f51])).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(equality_resolution,[],[f47])).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f31])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(nnf_transformation,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(flattening,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.18/0.47    inference(ennf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f54])).
% 0.18/0.47  fof(f131,plain,(
% 0.18/0.47    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_8),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f130])).
% 0.18/0.47  fof(f130,plain,(
% 0.18/0.47    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_8)),
% 0.18/0.47    inference(subsumption_resolution,[],[f129,f83])).
% 0.18/0.47  fof(f129,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl3_2 | ~spl3_3 | spl3_8)),
% 0.18/0.47    inference(backward_demodulation,[],[f126,f128])).
% 0.18/0.47  fof(f128,plain,(
% 0.18/0.47    sK2 = k7_relat_1(sK2,sK0) | (~spl3_2 | ~spl3_3)),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f65,f90,f42])).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(flattening,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    v4_relat_1(sK2,sK0) | ~spl3_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f88])).
% 0.18/0.47  fof(f88,plain,(
% 0.18/0.47    spl3_3 <=> v4_relat_1(sK2,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.47  fof(f126,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_8),
% 0.18/0.47    inference(avatar_component_clause,[],[f124])).
% 0.18/0.47  fof(f124,plain,(
% 0.18/0.47    spl3_8 <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.18/0.47  fof(f127,plain,(
% 0.18/0.47    ~spl3_8 | ~spl3_1 | ~spl3_2 | spl3_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f117,f93,f63,f54,f124])).
% 0.18/0.47  fof(f93,plain,(
% 0.18/0.47    spl3_4 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.47  fof(f117,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | (~spl3_1 | ~spl3_2 | spl3_4)),
% 0.18/0.47    inference(backward_demodulation,[],[f95,f116])).
% 0.18/0.47  fof(f116,plain,(
% 0.18/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.18/0.47    inference(forward_demodulation,[],[f109,f80])).
% 0.18/0.47  fof(f80,plain,(
% 0.18/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_partfun1(X0),sK2)) ) | ~spl3_2),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f65,f50])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f38,f34])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,axiom,(
% 0.18/0.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.18/0.47  fof(f109,plain,(
% 0.18/0.47    ( ! [X0] : (k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) ) | ~spl3_1),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f36,f56,f48])).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f27])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(flattening,[],[f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.18/0.47    inference(ennf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.18/0.47  fof(f95,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f93])).
% 0.18/0.47  fof(f122,plain,(
% 0.18/0.47    ~spl3_7 | ~spl3_1 | ~spl3_2 | spl3_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f115,f97,f63,f54,f119])).
% 0.18/0.47  fof(f97,plain,(
% 0.18/0.47    spl3_5 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.47  fof(f115,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.18/0.47    inference(backward_demodulation,[],[f99,f114])).
% 0.18/0.47  fof(f114,plain,(
% 0.18/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | (~spl3_1 | ~spl3_2)),
% 0.18/0.47    inference(forward_demodulation,[],[f110,f78])).
% 0.18/0.47  fof(f78,plain,(
% 0.18/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_partfun1(X0))) ) | ~spl3_2),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f65,f49])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))) )),
% 0.18/0.47    inference(definition_unfolding,[],[f37,f34])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.18/0.47  fof(f110,plain,(
% 0.18/0.47    ( ! [X0] : (k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | ~spl3_1),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f56,f36,f48])).
% 0.18/0.47  fof(f99,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f97])).
% 0.18/0.47  fof(f107,plain,(
% 0.18/0.47    spl3_6 | ~spl3_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f71,f54,f104])).
% 0.18/0.47  fof(f71,plain,(
% 0.18/0.47    v5_relat_1(sK2,sK1) | ~spl3_1),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f56,f45])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.47  fof(f100,plain,(
% 0.18/0.47    ~spl3_4 | ~spl3_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f33,f97,f93])).
% 0.18/0.47  fof(f33,plain,(
% 0.18/0.47    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f13])).
% 0.18/0.47  fof(f13,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.18/0.47    inference(negated_conjecture,[],[f12])).
% 0.18/0.47  fof(f12,conjecture,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 0.18/0.47  fof(f91,plain,(
% 0.18/0.47    spl3_3 | ~spl3_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f67,f54,f88])).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    v4_relat_1(sK2,sK0) | ~spl3_1),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f56,f44])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f66,plain,(
% 0.18/0.47    spl3_2 | ~spl3_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f58,f54,f63])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f56,f43])).
% 0.18/0.47  fof(f43,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.47  fof(f57,plain,(
% 0.18/0.47    spl3_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f32,f54])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (20462)------------------------------
% 0.18/0.47  % (20462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (20462)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (20462)Memory used [KB]: 10874
% 0.18/0.47  % (20462)Time elapsed: 0.077 s
% 0.18/0.47  % (20462)------------------------------
% 0.18/0.47  % (20462)------------------------------
% 0.18/0.47  % (20441)Success in time 0.134 s
%------------------------------------------------------------------------------
