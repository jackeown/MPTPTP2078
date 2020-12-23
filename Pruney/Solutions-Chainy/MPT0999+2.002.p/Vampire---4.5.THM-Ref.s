%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 127 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 ( 342 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f50,f58,f62,f70,f74,f78,f84,f96,f103,f110,f119,f124,f134,f137])).

fof(f137,plain,
    ( spl4_1
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_1
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f135,f123])).

fof(f123,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_19
  <=> ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f135,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,sK2),sK0)
    | spl4_1
    | ~ spl4_21 ),
    inference(superposition,[],[f35,f133])).

fof(f133,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_21
  <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f35,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_1
  <=> r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( spl4_21
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f130,f76,f38,f132])).

fof(f38,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f76,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f130,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f77,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f124,plain,
    ( spl4_19
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f120,f117,f100,f122])).

fof(f100,plain,
    ( spl4_15
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f117,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(sK3,X0),X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f120,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0)
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(resolution,[],[f118,f102])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK3),X1)
        | r1_tarski(k10_relat_1(sK3,X0),X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl4_18
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f115,f108,f81,f117])).

fof(f81,plain,
    ( spl4_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f108,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | r1_tarski(k10_relat_1(X0,X2),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(sK3,X0),X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) )
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(X0,X2),X1)
        | ~ r1_tarski(k1_relat_1(X0),X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f105,f72,f48,f108])).

fof(f48,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | r1_tarski(k10_relat_1(X0,X2),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f103,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f98,f93,f81,f56,f100])).

fof(f56,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f93,plain,
    ( spl4_14
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f98,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f97,f83])).

fof(f97,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f95,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f91,f68,f38,f93])).

fof(f68,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f91,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f69,f40])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f84,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f79,f60,f38,f81])).

fof(f60,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f61,f40])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f78,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f74,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f70,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f62,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f58,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f36,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.33  % Computer   : n017.cluster.edu
% 0.15/0.33  % Model      : x86_64 x86_64
% 0.15/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.33  % Memory     : 8042.1875MB
% 0.15/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.33  % CPULimit   : 60
% 0.15/0.33  % WCLimit    : 600
% 0.15/0.33  % DateTime   : Tue Dec  1 12:12:01 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.41  % (28641)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (28640)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (28640)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f36,f41,f50,f58,f62,f70,f74,f78,f84,f96,f103,f110,f119,f124,f134,f137])).
% 0.21/0.42  fof(f137,plain,(
% 0.21/0.42    spl4_1 | ~spl4_19 | ~spl4_21),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_19 | ~spl4_21)),
% 0.21/0.42    inference(subsumption_resolution,[],[f135,f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(sK3,X0),sK0)) ) | ~spl4_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f122])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    spl4_19 <=> ! [X0] : r1_tarski(k10_relat_1(sK3,X0),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    ~r1_tarski(k10_relat_1(sK3,sK2),sK0) | (spl4_1 | ~spl4_21)),
% 0.21/0.42    inference(superposition,[],[f35,f133])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f132])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl4_21 <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    spl4_21 | ~spl4_2 | ~spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f130,f76,f38,f132])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl4_11 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | (~spl4_2 | ~spl4_11)),
% 0.21/0.42    inference(resolution,[],[f77,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    spl4_19 | ~spl4_15 | ~spl4_18),
% 0.21/0.42    inference(avatar_split_clause,[],[f120,f117,f100,f122])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    spl4_15 <=> r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    spl4_18 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(sK3,X0),X1) | ~r1_tarski(k1_relat_1(sK3),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(sK3,X0),sK0)) ) | (~spl4_15 | ~spl4_18)),
% 0.21/0.42    inference(resolution,[],[f118,f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK3),sK0) | ~spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f100])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X1) | r1_tarski(k10_relat_1(sK3,X0),X1)) ) | ~spl4_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f117])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl4_18 | ~spl4_12 | ~spl4_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f115,f108,f81,f117])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl4_12 <=> v1_relat_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    spl4_16 <=> ! [X1,X0,X2] : (~r1_tarski(k1_relat_1(X0),X1) | r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK3,X0),X1) | ~r1_tarski(k1_relat_1(sK3),X1)) ) | (~spl4_12 | ~spl4_16)),
% 0.21/0.42    inference(resolution,[],[f109,f83])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    v1_relat_1(sK3) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X2),X1) | ~r1_tarski(k1_relat_1(X0),X1)) ) | ~spl4_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f108])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    spl4_16 | ~spl4_4 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f105,f72,f48,f108])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl4_4 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_relat_1(X0)) ) | (~spl4_4 | ~spl4_10)),
% 0.21/0.42    inference(resolution,[],[f73,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f72])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl4_15 | ~spl4_6 | ~spl4_12 | ~spl4_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f98,f93,f81,f56,f100])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl4_6 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl4_14 <=> v4_relat_1(sK3,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK3),sK0) | (~spl4_6 | ~spl4_12 | ~spl4_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f97,f83])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | (~spl4_6 | ~spl4_14)),
% 0.21/0.42    inference(resolution,[],[f95,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    v4_relat_1(sK3,sK0) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f93])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl4_14 | ~spl4_2 | ~spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f91,f68,f38,f93])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_9 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    v4_relat_1(sK3,sK0) | (~spl4_2 | ~spl4_9)),
% 0.21/0.42    inference(resolution,[],[f69,f40])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl4_12 | ~spl4_2 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f79,f60,f38,f81])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    v1_relat_1(sK3) | (~spl4_2 | ~spl4_7)),
% 0.21/0.42    inference(resolution,[],[f61,f40])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f31,f76])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f72])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f68])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f60])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(nnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f48])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f38])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f33])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ~r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (28640)------------------------------
% 0.21/0.42  % (28640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (28640)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (28640)Memory used [KB]: 10618
% 0.21/0.42  % (28640)Time elapsed: 0.008 s
% 0.21/0.42  % (28640)------------------------------
% 0.21/0.42  % (28640)------------------------------
% 0.21/0.43  % (28629)Success in time 0.077 s
%------------------------------------------------------------------------------
