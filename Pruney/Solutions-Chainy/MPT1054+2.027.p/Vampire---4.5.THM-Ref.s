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
% DateTime   : Thu Dec  3 13:07:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 237 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 393 expanded)
%              Number of equality atoms :   66 ( 163 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f81,f89,f148,f170,f182,f186])).

fof(f186,plain,
    ( spl2_9
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl2_9
    | ~ spl2_10 ),
    inference(global_subsumption,[],[f169,f183])).

fof(f183,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_10 ),
    inference(superposition,[],[f181,f95])).

fof(f95,plain,(
    ! [X0] : k9_relat_1(k6_partfun1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f94,f65])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f35])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f94,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = k9_relat_1(k6_partfun1(X0),X0) ),
    inference(superposition,[],[f90,f92])).

fof(f92,plain,(
    ! [X0] : k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X0) ),
    inference(unit_resulting_resolution,[],[f59,f63,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f63,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f90,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f181,plain,
    ( ! [X0] : k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl2_10
  <=> ! [X0] : k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f169,plain,
    ( sK1 != k9_relat_1(k6_partfun1(sK0),sK1)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_9
  <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f182,plain,
    ( spl2_10
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f177,f145,f180])).

fof(f145,plain,
    ( spl2_8
  <=> k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f177,plain,
    ( ! [X0] : k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f175,f151])).

fof(f151,plain,(
    ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f149,f57])).

fof(f57,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f36,f35,f35])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f149,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f59,f60,f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f38,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f40,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f175,plain,
    ( ! [X0] : k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0)) = k10_relat_1(k6_partfun1(sK1),X0)
    | ~ spl2_8 ),
    inference(superposition,[],[f158,f147])).

fof(f147,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f158,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X1),X2)) ),
    inference(forward_demodulation,[],[f157,f151])).

fof(f157,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X1),X2)) ),
    inference(forward_demodulation,[],[f155,f151])).

fof(f155,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k10_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X1),X2)) ),
    inference(unit_resulting_resolution,[],[f59,f59,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f170,plain,
    ( ~ spl2_9
    | spl2_3 ),
    inference(avatar_split_clause,[],[f165,f86,f167])).

fof(f86,plain,
    ( spl2_3
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f165,plain,
    ( sK1 != k9_relat_1(k6_partfun1(sK0),sK1)
    | spl2_3 ),
    inference(superposition,[],[f88,f163])).

fof(f163,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f160,f151])).

fof(f160,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f88,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f148,plain,
    ( spl2_8
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f140,f78,f145])).

fof(f78,plain,
    ( spl2_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f140,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f80,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f138,f66])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f35])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_partfun1(X0)),X1)
      | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ) ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f49,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f80,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f89,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f81,plain,
    ( spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f73,f69,f78])).

fof(f69,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f73,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f71,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (23593)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.43  % (23593)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f189,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f72,f81,f89,f148,f170,f182,f186])).
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    spl2_9 | ~spl2_10),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    $false | (spl2_9 | ~spl2_10)),
% 0.20/0.43    inference(global_subsumption,[],[f169,f183])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | ~spl2_10),
% 0.20/0.43    inference(superposition,[],[f181,f95])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k6_partfun1(X0),X0) = X0) )),
% 0.20/0.43    inference(forward_demodulation,[],[f94,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f47,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,axiom,(
% 0.20/0.43    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = k9_relat_1(k6_partfun1(X0),X0)) )),
% 0.20/0.43    inference(superposition,[],[f90,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0] : (k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X0)) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f59,f63,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f42,f35])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f37,f35])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f59,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0))) ) | ~spl2_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f180])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    spl2_10 <=> ! [X0] : k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    sK1 != k9_relat_1(k6_partfun1(sK0),sK1) | spl2_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f167])).
% 0.20/0.43  fof(f167,plain,(
% 0.20/0.43    spl2_9 <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.43  fof(f182,plain,(
% 0.20/0.43    spl2_10 | ~spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f177,f145,f180])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    spl2_8 <=> k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0))) ) | ~spl2_8),
% 0.20/0.43    inference(forward_demodulation,[],[f175,f151])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f149,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f36,f35,f35])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1)) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f59,f60,f58,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f38,f35])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f40,f35])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0)) = k10_relat_1(k6_partfun1(sK1),X0)) ) | ~spl2_8),
% 0.20/0.43    inference(superposition,[],[f158,f147])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1)) | ~spl2_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f145])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X1),X2))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f157,f151])).
% 0.20/0.43  fof(f157,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X1),X2))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f155,f151])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k10_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X1),X2))) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f59,f59,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.20/0.43  fof(f170,plain,(
% 0.20/0.43    ~spl2_9 | spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f165,f86,f167])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    spl2_3 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f165,plain,(
% 0.20/0.43    sK1 != k9_relat_1(k6_partfun1(sK0),sK1) | spl2_3),
% 0.20/0.43    inference(superposition,[],[f88,f163])).
% 0.20/0.43  fof(f163,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f160,f151])).
% 0.20/0.43  fof(f160,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f45,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f86])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    spl2_8 | ~spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f140,f78,f145])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl2_2 <=> r1_tarski(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1)) | ~spl2_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f80,f139])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f138,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f46,f35])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_partfun1(X0)),X1) | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) )),
% 0.20/0.43    inference(resolution,[],[f67,f59])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.20/0.43    inference(definition_unfolding,[],[f49,f35])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    r1_tarski(sK1,sK0) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ~spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f86])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.43    inference(negated_conjecture,[],[f16])).
% 0.20/0.43  fof(f16,conjecture,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl2_2 | ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f73,f69,f78])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    r1_tarski(sK1,sK0) | ~spl2_1),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f71,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f69])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f33,f69])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (23593)------------------------------
% 0.20/0.44  % (23593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23593)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (23593)Memory used [KB]: 10746
% 0.20/0.44  % (23593)Time elapsed: 0.035 s
% 0.20/0.44  % (23593)------------------------------
% 0.20/0.44  % (23593)------------------------------
% 0.20/0.44  % (23575)Success in time 0.084 s
%------------------------------------------------------------------------------
