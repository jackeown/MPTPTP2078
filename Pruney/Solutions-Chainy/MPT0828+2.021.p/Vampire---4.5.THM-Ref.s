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
% DateTime   : Thu Dec  3 12:56:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 145 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 373 expanded)
%              Number of equality atoms :   38 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f56,f60,f90,f92,f94,f177,f240])).

fof(f240,plain,
    ( spl3_2
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl3_2
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,
    ( sK1 != sK1
    | spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f74,f213])).

fof(f213,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f191,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f191,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f30,f176])).

fof(f176,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_8
  <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f47,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f177,plain,
    ( ~ spl3_3
    | spl3_8 ),
    inference(avatar_split_clause,[],[f173,f175,f51])).

fof(f51,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f173,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f166,f158])).

fof(f158,plain,(
    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(resolution,[],[f115,f28])).

fof(f28,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,(
    ! [X10] :
      ( ~ r1_tarski(k6_relat_1(X10),sK2)
      | k6_relat_1(X10) = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(X10)) ) ),
    inference(resolution,[],[f71,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2) ) ),
    inference(global_subsumption,[],[f27,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    inference(superposition,[],[f40,f73])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f29,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(superposition,[],[f35,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f166,plain,
    ( ~ v1_relat_1(sK2)
    | k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(resolution,[],[f99,f65])).

fof(f65,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f39,f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(k6_relat_1(k1_relat_1(X0)),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(global_subsumption,[],[f29,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(superposition,[],[f34,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f94,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f86,f27])).

fof(f86,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f89,f28])).

fof(f89,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_6
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f80,f43,f88,f85])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(resolution,[],[f41,f44])).

fof(f44,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_4
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f54,f51])).

fof(f49,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f48,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f46,f43])).

fof(f26,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:21:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (25913)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (25919)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.47  % (25913)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f48,f56,f60,f90,f92,f94,f177,f240])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    spl3_2 | ~spl3_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f239])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    $false | (spl3_2 | ~spl3_8)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f231])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    sK1 != sK1 | (spl3_2 | ~spl3_8)),
% 0.20/0.49    inference(superposition,[],[f74,f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    sK1 = k1_relat_1(sK2) | ~spl3_8),
% 0.20/0.49    inference(forward_demodulation,[],[f191,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~spl3_8),
% 0.20/0.49    inference(superposition,[],[f30,f176])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f175])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    spl3_8 <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    sK1 != k1_relat_1(sK2) | spl3_2),
% 0.20/0.49    inference(superposition,[],[f47,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f38,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    sK1 != k1_relset_1(sK1,sK0,sK2) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl3_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ~spl3_3 | spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f173,f175,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f166,f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))),
% 0.20/0.49    inference(resolution,[],[f115,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X10] : (~r1_tarski(k6_relat_1(X10),sK2) | k6_relat_1(X10) = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(X10))) )),
% 0.20/0.49    inference(resolution,[],[f71,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k6_relat_1(X0),sK2)) )),
% 0.20/0.49    inference(global_subsumption,[],[f27,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k6_relat_1(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) )),
% 0.20/0.49    inference(superposition,[],[f40,f73])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.20/0.49    inference(global_subsumption,[],[f29,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f35,f30])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))),
% 0.20/0.49    inference(resolution,[],[f99,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    v4_relat_1(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f39,f27])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_relat_1(X0,X1) | ~v1_relat_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(k6_relat_1(k1_relat_1(X0)),k6_relat_1(X1))) )),
% 0.20/0.49    inference(resolution,[],[f67,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.49    inference(global_subsumption,[],[f29,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.49    inference(superposition,[],[f34,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    $false | spl3_5),
% 0.20/0.49    inference(resolution,[],[f86,f27])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    $false | spl3_6),
% 0.20/0.49    inference(resolution,[],[f89,f28])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ~r1_tarski(k6_relat_1(sK1),sK2) | spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_6 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~spl3_5 | ~spl3_6 | spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f80,f43,f88,f85])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl3_1 <=> r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ~r1_tarski(k6_relat_1(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.20/0.49    inference(resolution,[],[f41,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f43])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    $false | spl3_4),
% 0.20/0.49    inference(resolution,[],[f55,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_4 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_3 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f54,f51])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f32,f27])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f46,f43])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    sK1 != k1_relset_1(sK1,sK0,sK2) | ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (25913)------------------------------
% 0.20/0.49  % (25913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25920)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (25913)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (25913)Memory used [KB]: 10746
% 0.20/0.49  % (25913)Time elapsed: 0.068 s
% 0.20/0.49  % (25913)------------------------------
% 0.20/0.49  % (25913)------------------------------
% 0.20/0.49  % (25900)Success in time 0.143 s
%------------------------------------------------------------------------------
