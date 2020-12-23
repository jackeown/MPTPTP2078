%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 377 expanded)
%              Number of equality atoms :   38 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f57,f61,f86,f88,f95,f177,f240])).

fof(f240,plain,
    ( spl3_1
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl3_1
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,
    ( sK1 != sK1
    | spl3_1
    | ~ spl3_8 ),
    inference(superposition,[],[f75,f213])).

fof(f213,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f191,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f191,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f31,f176])).

fof(f176,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_8
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f45,f74])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f45,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f177,plain,
    ( ~ spl3_3
    | spl3_8 ),
    inference(avatar_split_clause,[],[f173,f175,f52])).

fof(f52,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f173,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f166,f151])).

fof(f151,plain,(
    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f116,f29])).

fof(f29,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,(
    ! [X10] :
      ( ~ r1_tarski(k6_relat_1(X10),sK2)
      | k6_relat_1(X10) = k5_relat_1(k6_relat_1(X10),k6_relat_1(k2_relat_1(sK2))) ) ),
    inference(resolution,[],[f72,f93])).

fof(f93,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2) ) ),
    inference(global_subsumption,[],[f28,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f42,f74])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(global_subsumption,[],[f30,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f166,plain,
    ( ~ v1_relat_1(sK2)
    | k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(X0))) ) ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f30,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f82,f28])).

fof(f82,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f88,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f85,f29])).

fof(f85,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_6
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f86,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f76,f47,f84,f81])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f76,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f50,f55,f52])).

fof(f50,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f49,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f27,f47,f44])).

fof(f27,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:27:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.43  % (26712)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.45  % (26719)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.46  % (26720)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.46  % (26719)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (26711)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f241,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f49,f57,f61,f86,f88,f95,f177,f240])).
% 0.19/0.48  fof(f240,plain,(
% 0.19/0.48    spl3_1 | ~spl3_8),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f239])).
% 0.19/0.48  fof(f239,plain,(
% 0.19/0.48    $false | (spl3_1 | ~spl3_8)),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f231])).
% 0.19/0.48  fof(f231,plain,(
% 0.19/0.48    sK1 != sK1 | (spl3_1 | ~spl3_8)),
% 0.19/0.48    inference(superposition,[],[f75,f213])).
% 0.19/0.48  fof(f213,plain,(
% 0.19/0.48    sK1 = k2_relat_1(sK2) | ~spl3_8),
% 0.19/0.48    inference(forward_demodulation,[],[f191,f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.48  fof(f191,plain,(
% 0.19/0.48    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~spl3_8),
% 0.19/0.48    inference(superposition,[],[f31,f176])).
% 0.19/0.48  fof(f176,plain,(
% 0.19/0.48    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f175])).
% 0.19/0.48  fof(f175,plain,(
% 0.19/0.48    spl3_8 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    sK1 != k2_relat_1(sK2) | spl3_1),
% 0.19/0.48    inference(superposition,[],[f45,f74])).
% 0.19/0.48  fof(f74,plain,(
% 0.19/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.19/0.48    inference(resolution,[],[f39,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(flattening,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.19/0.48    inference(negated_conjecture,[],[f11])).
% 0.19/0.48  fof(f11,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    spl3_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f177,plain,(
% 0.19/0.48    ~spl3_3 | spl3_8),
% 0.19/0.48    inference(avatar_split_clause,[],[f173,f175,f52])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    spl3_3 <=> v1_relat_1(sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.48  fof(f173,plain,(
% 0.19/0.48    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.19/0.48    inference(forward_demodulation,[],[f166,f151])).
% 0.19/0.48  fof(f151,plain,(
% 0.19/0.48    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(k2_relat_1(sK2)))),
% 0.19/0.48    inference(resolution,[],[f116,f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    ( ! [X10] : (~r1_tarski(k6_relat_1(X10),sK2) | k6_relat_1(X10) = k5_relat_1(k6_relat_1(X10),k6_relat_1(k2_relat_1(sK2)))) )),
% 0.19/0.48    inference(resolution,[],[f72,f93])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK2)) | ~r1_tarski(k6_relat_1(X0),sK2)) )),
% 0.19/0.48    inference(global_subsumption,[],[f28,f92])).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK2)) | ~r1_tarski(k6_relat_1(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.19/0.48    inference(superposition,[],[f42,f74])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(flattening,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.19/0.48    inference(global_subsumption,[],[f30,f70])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.19/0.48    inference(superposition,[],[f36,f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.48    inference(pure_predicate_removal,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.48  fof(f166,plain,(
% 0.19/0.48    ~v1_relat_1(sK2) | k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(k2_relat_1(sK2)))),
% 0.19/0.48    inference(resolution,[],[f100,f66])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    v5_relat_1(sK2,sK1)),
% 0.19/0.48    inference(resolution,[],[f40,f28])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v5_relat_1(X0,X1) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(X0)))) )),
% 0.19/0.48    inference(resolution,[],[f68,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.19/0.48    inference(global_subsumption,[],[f30,f67])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.19/0.48    inference(superposition,[],[f35,f31])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.19/0.48  fof(f95,plain,(
% 0.19/0.48    spl3_5),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f94])).
% 0.19/0.48  fof(f94,plain,(
% 0.19/0.48    $false | spl3_5),
% 0.19/0.48    inference(resolution,[],[f82,f28])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f81])).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.48  fof(f88,plain,(
% 0.19/0.48    spl3_6),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f87])).
% 0.19/0.48  fof(f87,plain,(
% 0.19/0.48    $false | spl3_6),
% 0.19/0.48    inference(resolution,[],[f85,f29])).
% 0.19/0.48  fof(f85,plain,(
% 0.19/0.48    ~r1_tarski(k6_relat_1(sK1),sK2) | spl3_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f84])).
% 0.19/0.48  fof(f84,plain,(
% 0.19/0.48    spl3_6 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.48  fof(f86,plain,(
% 0.19/0.48    ~spl3_5 | ~spl3_6 | spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f76,f47,f84,f81])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    spl3_2 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    ~r1_tarski(k6_relat_1(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.19/0.48    inference(resolution,[],[f41,f48])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f47])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    spl3_4),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f60])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    $false | spl3_4),
% 0.19/0.48    inference(resolution,[],[f56,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f55])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    spl3_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    spl3_3 | ~spl3_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f50,f55,f52])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.19/0.48    inference(resolution,[],[f33,f28])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    ~spl3_1 | ~spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f27,f47,f44])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (26719)------------------------------
% 0.19/0.48  % (26719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (26719)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (26719)Memory used [KB]: 10746
% 0.19/0.48  % (26719)Time elapsed: 0.065 s
% 0.19/0.48  % (26719)------------------------------
% 0.19/0.48  % (26719)------------------------------
% 0.19/0.48  % (26706)Success in time 0.142 s
%------------------------------------------------------------------------------
