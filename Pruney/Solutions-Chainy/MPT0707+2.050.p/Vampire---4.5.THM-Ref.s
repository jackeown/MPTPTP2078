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
% DateTime   : Thu Dec  3 12:54:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 136 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :  219 ( 331 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f71,f78,f84,f90,f95,f100,f105,f108])).

fof(f108,plain,
    ( spl2_1
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl2_1
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f31,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f106,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(superposition,[],[f104,f77])).

fof(f77,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_11
  <=> ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f104,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_16
  <=> ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f105,plain,
    ( spl2_16
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f101,f98,f87,f103])).

fof(f87,plain,
    ( spl2_13
  <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f98,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f101,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(superposition,[],[f99,f89])).

fof(f89,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f99,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f96,f93,f39,f98])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f93,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f96,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f94,f40])).

fof(f40,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f91,f59,f39,f93])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f90,plain,
    ( spl2_13
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f85,f82,f68,f87])).

fof(f68,plain,
    ( spl2_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f82,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f85,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(resolution,[],[f83,f70])).

fof(f70,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f80,f55,f43,f39,f82])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f56,f44])).

fof(f44,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f78,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f74,f51,f47,f43,f39,f76])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f74,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f73,f44])).

fof(f73,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f72,f48])).

fof(f48,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f72,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f71,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f66,f63,f34,f68])).

fof(f34,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f66,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.39  % (18990)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (18992)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.42  % (18989)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (18993)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (18993)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f71,f78,f84,f90,f95,f100,f105,f108])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    spl2_1 | ~spl2_11 | ~spl2_16),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    $false | (spl2_1 | ~spl2_11 | ~spl2_16)),
% 0.20/0.42    inference(subsumption_resolution,[],[f106,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl2_11 | ~spl2_16)),
% 0.20/0.42    inference(superposition,[],[f104,f77])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) ) | ~spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f76])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl2_11 <=> ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))) ) | ~spl2_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f103])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    spl2_16 <=> ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    spl2_16 | ~spl2_13 | ~spl2_15),
% 0.20/0.42    inference(avatar_split_clause,[],[f101,f98,f87,f103])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl2_13 <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    spl2_15 <=> ! [X1,X0,X2] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.42  fof(f101,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))) ) | (~spl2_13 | ~spl2_15)),
% 0.20/0.42    inference(superposition,[],[f99,f89])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | ~spl2_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | ~spl2_15),
% 0.20/0.42    inference(avatar_component_clause,[],[f98])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    spl2_15 | ~spl2_3 | ~spl2_14),
% 0.20/0.42    inference(avatar_split_clause,[],[f96,f93,f39,f98])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    spl2_14 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.42  fof(f96,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | (~spl2_3 | ~spl2_14)),
% 0.20/0.42    inference(resolution,[],[f94,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2))) ) | ~spl2_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f93])).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    spl2_14 | ~spl2_3 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f91,f59,f39,f93])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl2_8 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f60,f40])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f59])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    spl2_13 | ~spl2_10 | ~spl2_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f85,f82,f68,f87])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_10 <=> r1_tarski(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl2_12 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | (~spl2_10 | ~spl2_12)),
% 0.20/0.42    inference(resolution,[],[f83,f70])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    r1_tarski(sK1,sK0) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f68])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | ~spl2_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f82])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl2_12 | ~spl2_3 | ~spl2_4 | ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f80,f55,f43,f39,f82])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl2_7 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.20/0.42    inference(subsumption_resolution,[],[f79,f40])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_4 | ~spl2_7)),
% 0.20/0.42    inference(superposition,[],[f56,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl2_11 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f74,f51,f47,f43,f39,f76])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl2_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl2_6 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6)),
% 0.20/0.42    inference(forward_demodulation,[],[f73,f44])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.20/0.42    inference(forward_demodulation,[],[f72,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f47])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_6)),
% 0.20/0.42    inference(resolution,[],[f52,f40])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f51])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl2_10 | ~spl2_2 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f66,f63,f34,f68])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl2_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_9)),
% 0.20/0.42    inference(resolution,[],[f64,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f63])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f63])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.42    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f59])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f55])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f51])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f47])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f43])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f39])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.42    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f34])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f29])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (18993)------------------------------
% 0.20/0.42  % (18993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (18993)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (18993)Memory used [KB]: 6140
% 0.20/0.42  % (18993)Time elapsed: 0.028 s
% 0.20/0.42  % (18993)------------------------------
% 0.20/0.42  % (18993)------------------------------
% 0.20/0.43  % (18982)Success in time 0.076 s
%------------------------------------------------------------------------------
