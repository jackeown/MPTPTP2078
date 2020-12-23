%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 152 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  238 ( 363 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f62,f71,f80,f89,f102,f123,f132,f152])).

fof(f152,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f150,f131])).

fof(f131,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f150,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f149,f101])).

fof(f101,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_6
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f149,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f147,f148])).

fof(f148,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f138,f107])).

fof(f107,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_partfun1(X0),sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f61,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f138,plain,
    ( ! [X0] : k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f46,f52,f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f147,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f146,f131])).

fof(f146,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f145,f122])).

fof(f122,plain,
    ( sK2 = k8_relat_1(sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_7
  <=> sK2 = k8_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f145,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f32,f144])).

fof(f144,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f139,f103])).

fof(f103,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_partfun1(X0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f47])).

% (4416)Refutation not found, incomplete strategy% (4416)------------------------------
% (4416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) ) ),
    inference(definition_unfolding,[],[f35,f33])).

% (4416)Termination reason: Refutation not found, incomplete strategy

% (4416)Memory used [KB]: 10618
% (4416)Time elapsed: 0.058 s
% (4416)------------------------------
% (4416)------------------------------
fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f139,plain,
    ( ! [X0] : k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f46,f45])).

fof(f32,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f132,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f124,f50,f129])).

fof(f124,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f52,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f123,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f115,f86,f59,f120])).

fof(f86,plain,
    ( spl3_5
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( sK2 = k8_relat_1(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f61,f88,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f88,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f102,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f94,f68,f59,f99])).

fof(f68,plain,
    ( spl3_3
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f94,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f70,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f70,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f89,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f81,f77,f59,f86])).

fof(f77,plain,
    ( spl3_4
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f61,f79,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f79,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f72,f50,f77])).

fof(f72,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f71,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f63,f50,f68])).

fof(f63,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f50,f59])).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (4413)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (4416)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (4413)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f53,f62,f71,f80,f89,f102,f123,f132,f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f150,f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl3_8 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f149,f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    sK2 = k7_relat_1(sK2,sK0) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl3_6 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(backward_demodulation,[],[f147,f148])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(forward_demodulation,[],[f138,f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_partfun1(X0),sK2)) ) | ~spl3_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f36,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl3_2 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0] : (k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) ) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f46,f52,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f34,f33])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f146,f131])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.20/0.49    inference(forward_demodulation,[],[f145,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    sK2 = k8_relat_1(sK1,sK2) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl3_7 <=> sK2 = k8_relat_1(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | (~spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(backward_demodulation,[],[f32,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X0] : (k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(forward_demodulation,[],[f139,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_partfun1(X0))) ) | ~spl3_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f47])).
% 0.20/0.49  % (4416)Refutation not found, incomplete strategy% (4416)------------------------------
% 0.20/0.49  % (4416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f35,f33])).
% 0.20/0.49  % (4416)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4416)Memory used [KB]: 10618
% 0.20/0.49  % (4416)Time elapsed: 0.058 s
% 0.20/0.49  % (4416)------------------------------
% 0.20/0.49  % (4416)------------------------------
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0] : (k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f46,f45])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl3_8 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f124,f50,f129])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f52,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl3_7 | ~spl3_2 | ~spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f115,f86,f59,f120])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_5 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    sK2 = k8_relat_1(sK1,sK2) | (~spl3_2 | ~spl3_5)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f88,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl3_6 | ~spl3_2 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f94,f68,f59,f99])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_3 <=> v4_relat_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    sK2 = k7_relat_1(sK2,sK0) | (~spl3_2 | ~spl3_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f70,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    v4_relat_1(sK2,sK0) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl3_5 | ~spl3_2 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f81,f77,f59,f86])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl3_4 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_2 | ~spl3_4)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f79,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_4 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f50,f77])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl3_3 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f63,f50,f68])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v4_relat_1(sK2,sK0) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl3_2 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f50,f59])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f50])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (4413)------------------------------
% 0.20/0.49  % (4413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4413)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (4413)Memory used [KB]: 6140
% 0.20/0.49  % (4413)Time elapsed: 0.078 s
% 0.20/0.49  % (4413)------------------------------
% 0.20/0.49  % (4413)------------------------------
% 0.20/0.49  % (4409)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (4404)Success in time 0.136 s
%------------------------------------------------------------------------------
