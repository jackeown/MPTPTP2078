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
% DateTime   : Thu Dec  3 13:07:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 144 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  239 ( 338 expanded)
%              Number of equality atoms :   51 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f59,f67,f72,f76,f80,f87,f95,f102,f110,f115,f121,f125,f133,f138])).

fof(f138,plain,
    ( ~ spl2_10
    | ~ spl2_13
    | spl2_17
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl2_10
    | ~ spl2_13
    | spl2_17
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f136,f120])).

fof(f120,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_17
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f136,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f134,f101])).

fof(f101,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_13
  <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f134,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1))
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(resolution,[],[f132,f86])).

fof(f86,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f133,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f129,f123,f65,f52,f48,f44,f131])).

fof(f44,plain,
    ( spl2_1
  <=> ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( spl2_3
  <=> ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f65,plain,
    ( spl2_6
  <=> ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f123,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
        | ~ v2_funct_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f128,f66])).

fof(f66,plain,
    ( ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
        | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f49,plain,
    ( ! [X0] : v1_relat_1(k6_partfun1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
        | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
        | ~ v1_relat_1(k6_partfun1(X0)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f45,plain,
    ( ! [X0] : v1_funct_1(k6_partfun1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
        | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
        | ~ v1_funct_1(k6_partfun1(X0))
        | ~ v1_relat_1(k6_partfun1(X0)) )
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(resolution,[],[f124,f53])).

fof(f53,plain,
    ( ! [X0] : v2_funct_1(k6_partfun1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X1)
        | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f33,f123])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f121,plain,
    ( ~ spl2_17
    | spl2_7
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f116,f113,f69,f118])).

fof(f69,plain,
    ( spl2_7
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f113,plain,
    ( spl2_16
  <=> ! [X1,X0] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f116,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_7
    | ~ spl2_16 ),
    inference(superposition,[],[f71,f114])).

fof(f114,plain,
    ( ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f113])).

fof(f71,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f115,plain,
    ( spl2_16
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f111,f108,f74,f113])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f108,plain,
    ( spl2_15
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f111,plain,
    ( ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(resolution,[],[f109,f75])).

fof(f75,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f109,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f35,f108])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f102,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f96,f93,f56,f99])).

fof(f56,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f93,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k9_relat_1(k6_partfun1(X0),X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f96,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f94,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k9_relat_1(k6_partfun1(X0),X1) = X1 )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f24,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f87,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f81,f78,f56,f84])).

fof(f78,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f81,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f72,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f23,f69])).

fof(f23,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f67,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f41,f65])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f24])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f52])).

fof(f38,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f48])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f46,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f36,f44])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (1304)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (1309)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (1309)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f46,f50,f54,f59,f67,f72,f76,f80,f87,f95,f102,f110,f115,f121,f125,f133,f138])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ~spl2_10 | ~spl2_13 | spl2_17 | ~spl2_19),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    $false | (~spl2_10 | ~spl2_13 | spl2_17 | ~spl2_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f136,f120])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl2_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f118])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl2_17 <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | (~spl2_10 | ~spl2_13 | ~spl2_19)),
% 0.21/0.46    inference(forward_demodulation,[],[f134,f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | ~spl2_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f99])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl2_13 <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1)) | (~spl2_10 | ~spl2_19)),
% 0.21/0.46    inference(resolution,[],[f132,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    r1_tarski(sK1,sK0) | ~spl2_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl2_10 <=> r1_tarski(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) ) | ~spl2_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f131])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl2_19 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl2_19 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f129,f123,f65,f52,f48,f44,f131])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl2_1 <=> ! [X0] : v1_funct_1(k6_partfun1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl2_2 <=> ! [X0] : v1_relat_1(k6_partfun1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl2_3 <=> ! [X0] : v2_funct_1(k6_partfun1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl2_6 <=> ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    spl2_18 <=> ! [X1,X0] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_18)),
% 0.21/0.46    inference(forward_demodulation,[],[f128,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) ) | ~spl2_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f65])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f127,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) ) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | ~v1_relat_1(k6_partfun1(X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f126,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) ) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) ) | (~spl2_3 | ~spl2_18)),
% 0.21/0.46    inference(resolution,[],[f124,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) ) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl2_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f123])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    spl2_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f123])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~spl2_17 | spl2_7 | ~spl2_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f116,f113,f69,f118])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl2_7 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl2_16 <=> ! [X1,X0] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | (spl2_7 | ~spl2_16)),
% 0.21/0.46    inference(superposition,[],[f71,f114])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) ) | ~spl2_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f113])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl2_16 | ~spl2_8 | ~spl2_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f111,f108,f74,f113])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl2_8 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    spl2_15 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) ) | (~spl2_8 | ~spl2_15)),
% 0.21/0.46    inference(resolution,[],[f109,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f74])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl2_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f108])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl2_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f108])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    spl2_13 | ~spl2_4 | ~spl2_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f96,f93,f56,f99])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl2_12 <=> ! [X1,X0] : (k9_relat_1(k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | (~spl2_4 | ~spl2_12)),
% 0.21/0.46    inference(resolution,[],[f94,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f56])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = X1) ) | ~spl2_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl2_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f42,f93])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f32,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl2_10 | ~spl2_4 | ~spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f81,f78,f56,f84])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl2_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    r1_tarski(sK1,sK0) | (~spl2_4 | ~spl2_9)),
% 0.21/0.46    inference(resolution,[],[f79,f58])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f78])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f78])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl2_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f74])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ~spl2_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f69])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f65])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f30,f24])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f56])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f52])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f28,f24])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f48])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f25,f24])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f44])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f26,f24])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (1309)------------------------------
% 0.21/0.46  % (1309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (1309)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (1309)Memory used [KB]: 6140
% 0.21/0.46  % (1309)Time elapsed: 0.058 s
% 0.21/0.46  % (1309)------------------------------
% 0.21/0.46  % (1309)------------------------------
% 0.21/0.46  % (1301)Success in time 0.108 s
%------------------------------------------------------------------------------
