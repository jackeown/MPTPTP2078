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
% DateTime   : Thu Dec  3 13:01:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 182 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :  271 ( 442 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f72,f74,f104,f113,f115,f117,f119,f129,f135,f141,f143,f149,f151,f154])).

fof(f154,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f128,f84])).

fof(f84,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f128,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_11
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f151,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f148,f80])).

fof(f80,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f148,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_14
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f149,plain,
    ( ~ spl3_4
    | ~ spl3_14
    | spl3_13 ),
    inference(avatar_split_clause,[],[f144,f138,f146,f69])).

fof(f69,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f138,plain,
    ( spl3_13
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f144,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(resolution,[],[f140,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f140,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f143,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f134,f78])).

fof(f78,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f134,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_12
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f141,plain,
    ( ~ spl3_4
    | ~ spl3_13
    | ~ spl3_11
    | spl3_9 ),
    inference(avatar_split_clause,[],[f136,f110,f126,f138,f69])).

fof(f110,plain,
    ( spl3_9
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f136,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(superposition,[],[f112,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f112,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f135,plain,
    ( ~ spl3_12
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f130,f122,f69,f132])).

fof(f122,plain,
    ( spl3_10
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_10 ),
    inference(resolution,[],[f124,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f124,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f129,plain,
    ( ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_7 ),
    inference(avatar_split_clause,[],[f120,f101,f126,f122,f69])).

fof(f101,plain,
    ( spl3_7
  <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f120,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(superposition,[],[f103,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f103,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f119,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f108,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_8
  <=> m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f117,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f95,f49])).

fof(f95,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_5
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f99,f33])).

fof(f99,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f113,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_2 ),
    inference(avatar_split_clause,[],[f91,f58,f110,f106,f97])).

fof(f58,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f91,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f60,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f104,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f90,f54,f101,f97,f93])).

fof(f54,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f56,f48])).

fof(f56,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f74,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f67,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_3
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f62,f69,f65])).

fof(f62,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f61,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f58,f54])).

fof(f34,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (20591)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (20583)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (20587)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (20584)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (20587)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f61,f72,f74,f104,f113,f115,f117,f119,f129,f135,f141,f143,f149,f151,f154])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    $false | spl3_11),
% 0.20/0.47    inference(resolution,[],[f128,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.47    inference(resolution,[],[f52,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.20/0.47    inference(negated_conjecture,[],[f13])).
% 0.20/0.47  fof(f13,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.20/0.47    inference(condensation,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl3_11 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    spl3_14),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    $false | spl3_14),
% 0.20/0.47    inference(resolution,[],[f148,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    v5_relat_1(sK2,sK1)),
% 0.20/0.47    inference(resolution,[],[f46,f33])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ~v5_relat_1(sK2,sK1) | spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_14 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_14 | spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f144,f138,f146,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl3_4 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl3_13 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl3_13),
% 0.20/0.47    inference(resolution,[],[f140,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f138])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    $false | spl3_12),
% 0.20/0.47    inference(resolution,[],[f134,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    v4_relat_1(sK2,sK0)),
% 0.20/0.47    inference(resolution,[],[f45,f33])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~v4_relat_1(sK2,sK0) | spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl3_12 <=> v4_relat_1(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_13 | ~spl3_11 | spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f136,f110,f126,f138,f69])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl3_9 <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | spl3_9),
% 0.20/0.47    inference(superposition,[],[f112,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f40,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f110])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~spl3_12 | ~spl3_4 | spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f130,f122,f69,f132])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl3_10 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_10),
% 0.20/0.47    inference(resolution,[],[f124,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(superposition,[],[f39,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f120,f101,f126,f122,f69])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl3_7 <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | spl3_7),
% 0.20/0.47    inference(superposition,[],[f103,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f41,f35])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    $false | spl3_8),
% 0.20/0.47    inference(resolution,[],[f108,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f35])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_8 <=> m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    $false | spl3_5),
% 0.20/0.47    inference(resolution,[],[f95,f49])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl3_5 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    $false | spl3_6),
% 0.20/0.47    inference(resolution,[],[f99,f33])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ~spl3_6 | ~spl3_8 | ~spl3_9 | spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f91,f58,f110,f106,f97])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl3_2 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.20/0.47    inference(superposition,[],[f60,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f90,f54,f101,f97,f93])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_1 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_1),
% 0.20/0.47    inference(superposition,[],[f56,f48])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    $false | spl3_3),
% 0.20/0.47    inference(resolution,[],[f67,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl3_3 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ~spl3_3 | spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f69,f65])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    inference(resolution,[],[f37,f33])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f58,f54])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (20587)------------------------------
% 0.20/0.47  % (20587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20587)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (20587)Memory used [KB]: 6140
% 0.20/0.47  % (20587)Time elapsed: 0.054 s
% 0.20/0.47  % (20587)------------------------------
% 0.20/0.47  % (20587)------------------------------
% 0.20/0.47  % (20582)Success in time 0.114 s
%------------------------------------------------------------------------------
