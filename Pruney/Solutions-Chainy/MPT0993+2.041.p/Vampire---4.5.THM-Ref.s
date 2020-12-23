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
% DateTime   : Thu Dec  3 13:03:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 130 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  255 ( 421 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f60,f67,f72,f79,f94,f105,f120,f124,f132,f140])).

fof(f140,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f138,f93])).

fof(f93,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_9
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f138,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl4_4
    | spl4_5
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f133,f131])).

fof(f131,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_16
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f133,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | ~ spl4_4
    | spl4_5
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f66,f127])).

fof(f127,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(resolution,[],[f123,f59])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f66,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f132,plain,
    ( spl4_16
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f126,f118,f76,f69,f129])).

fof(f69,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( spl4_7
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f118,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,sK0)
        | k7_relat_1(X0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f126,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f125,f71])).

fof(f71,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f125,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(resolution,[],[f119,f78])).

fof(f78,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(X0,sK0)
        | ~ v1_relat_1(X0)
        | k7_relat_1(X0,sK2) = X0 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f124,plain,
    ( spl4_15
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f95,f42,f122])).

fof(f42,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f120,plain,
    ( spl4_14
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f107,f103,f118])).

fof(f103,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ v4_relat_1(X0,sK0)
        | ~ v1_relat_1(X0)
        | v4_relat_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,sK0)
        | k7_relat_1(X0,sK2) = X0 )
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,sK0)
        | k7_relat_1(X0,sK2) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f104,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f104,plain,
    ( ! [X0] :
        ( v4_relat_1(X0,sK2)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,sK0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f88,f47,f103])).

fof(f47,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(X0,sK0)
        | ~ v1_relat_1(X0)
        | v4_relat_1(X0,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f32,f49])).

fof(f49,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | v4_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f94,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f89,f57,f91])).

fof(f89,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f40,f59])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f79,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f74,f57,f76])).

fof(f74,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f34,f59])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f72,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f62,f57,f69])).

fof(f62,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f61,f59])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f67,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
      & r1_tarski(sK0,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f47])).

fof(f28,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:35:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (31334)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (31324)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (31323)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (31326)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (31346)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (31326)Refutation not found, incomplete strategy% (31326)------------------------------
% 0.21/0.51  % (31326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31326)Memory used [KB]: 6140
% 0.21/0.51  % (31326)Time elapsed: 0.095 s
% 0.21/0.51  % (31326)------------------------------
% 0.21/0.51  % (31326)------------------------------
% 0.21/0.51  % (31323)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (31334)Refutation not found, incomplete strategy% (31334)------------------------------
% 0.21/0.52  % (31334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31334)Memory used [KB]: 6140
% 0.21/0.52  % (31334)Time elapsed: 0.101 s
% 0.21/0.52  % (31334)------------------------------
% 0.21/0.52  % (31334)------------------------------
% 0.21/0.52  % (31332)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (31330)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (31343)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (31335)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (31321)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f45,f50,f60,f67,f72,f79,f94,f105,f120,f124,f132,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~spl4_4 | spl4_5 | ~spl4_9 | ~spl4_15 | ~spl4_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    $false | (~spl4_4 | spl4_5 | ~spl4_9 | ~spl4_15 | ~spl4_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f138,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl4_9 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK1,sK3,sK3) | (~spl4_4 | spl4_5 | ~spl4_15 | ~spl4_16)),
% 0.21/0.52    inference(forward_demodulation,[],[f133,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,sK2) | ~spl4_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl4_16 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) | (~spl4_4 | spl4_5 | ~spl4_15)),
% 0.21/0.52    inference(backward_demodulation,[],[f66,f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_4 | ~spl4_15)),
% 0.21/0.52    inference(resolution,[],[f123,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl4_15 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) | spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl4_5 <=> r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl4_16 | ~spl4_6 | ~spl4_7 | ~spl4_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f126,f118,f76,f69,f129])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl4_6 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl4_7 <=> v4_relat_1(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl4_14 <=> ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,sK0) | k7_relat_1(X0,sK2) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,sK2) | (~spl4_6 | ~spl4_7 | ~spl4_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2) | (~spl4_7 | ~spl4_14)),
% 0.21/0.52    inference(resolution,[],[f119,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v4_relat_1(sK3,sK0) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(X0,sK0) | ~v1_relat_1(X0) | k7_relat_1(X0,sK2) = X0) ) | ~spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl4_15 | ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f95,f42,f122])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_1),
% 0.21/0.52    inference(resolution,[],[f36,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f42])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl4_14 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f107,f103,f118])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl4_11 <=> ! [X0] : (~v4_relat_1(X0,sK0) | ~v1_relat_1(X0) | v4_relat_1(X0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,sK0) | k7_relat_1(X0,sK2) = X0) ) | ~spl4_11),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,sK0) | k7_relat_1(X0,sK2) = X0 | ~v1_relat_1(X0)) ) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f104,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X0] : (v4_relat_1(X0,sK2) | ~v1_relat_1(X0) | ~v4_relat_1(X0,sK0)) ) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl4_11 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f88,f47,f103])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl4_2 <=> r1_tarski(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(X0,sK0) | ~v1_relat_1(X0) | v4_relat_1(X0,sK2)) ) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f32,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    r1_tarski(sK0,sK2) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f47])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | v4_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl4_9 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f89,f57,f91])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f40,f59])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl4_7 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f74,f57,f76])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    v4_relat_1(sK3,sK0) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f34,f59])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl4_6 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f57,f69])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f61,f59])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f30,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f64])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f47])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    r1_tarski(sK0,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f42])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31323)------------------------------
% 0.21/0.52  % (31323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31323)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31323)Memory used [KB]: 6140
% 0.21/0.52  % (31323)Time elapsed: 0.093 s
% 0.21/0.52  % (31323)------------------------------
% 0.21/0.52  % (31323)------------------------------
% 0.21/0.53  % (31319)Success in time 0.161 s
%------------------------------------------------------------------------------
