%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:12 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 377 expanded)
%              Number of leaves         :   47 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  551 (1299 expanded)
%              Number of equality atoms :  114 ( 266 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f801,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f124,f129,f170,f175,f220,f257,f302,f326,f368,f412,f481,f554,f581,f582,f596,f647,f671,f677,f705,f709,f710,f796,f799])).

fof(f799,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | spl4_12
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f798])).

fof(f798,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | spl4_12
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f600,f712])).

fof(f712,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_5
    | spl4_12 ),
    inference(forward_demodulation,[],[f169,f176])).

fof(f176,plain,
    ( ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f94,f114,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f169,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_12
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f600,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl4_46
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f796,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | spl4_46
    | ~ spl4_51 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | spl4_46
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f794,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f794,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_46
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f788,f703])).

fof(f703,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl4_51
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f788,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_46 ),
    inference(unit_resulting_resolution,[],[f333,f599,f465,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f465,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f333,f335,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f335,plain,
    ( ! [X0] : v5_relat_1(k7_relat_1(sK3,X0),sK1)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f180,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f180,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f178,f176])).

fof(f178,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f94,f114,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f599,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f598])).

fof(f333,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f180,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f710,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f709,plain,
    ( ~ spl4_2
    | ~ spl4_13
    | ~ spl4_42
    | spl4_51 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_42
    | spl4_51 ),
    inference(subsumption_resolution,[],[f707,f99])).

fof(f99,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f707,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl4_13
    | ~ spl4_42
    | spl4_51 ),
    inference(forward_demodulation,[],[f706,f564])).

fof(f564,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl4_42
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f706,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_13
    | spl4_51 ),
    inference(unit_resulting_resolution,[],[f174,f704,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

% (5035)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f704,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f702])).

fof(f174,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f705,plain,
    ( ~ spl4_51
    | spl4_49
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f678,f674,f668,f702])).

fof(f668,plain,
    ( spl4_49
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f674,plain,
    ( spl4_50
  <=> k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f678,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_49
    | ~ spl4_50 ),
    inference(superposition,[],[f670,f676])).

fof(f676,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f674])).

fof(f670,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f668])).

fof(f677,plain,
    ( spl4_50
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f603,f598,f674])).

fof(f603,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f600,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f671,plain,
    ( ~ spl4_49
    | spl4_6
    | spl4_45
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f605,f598,f593,f117,f668])).

fof(f117,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f593,plain,
    ( spl4_45
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f605,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_6
    | spl4_45
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f119,f595,f600,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f595,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f593])).

fof(f119,plain,
    ( k1_xboole_0 != sK1
    | spl4_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f647,plain,
    ( spl4_18
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f284,f117,f112,f107,f222])).

fof(f222,plain,
    ( spl4_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f107,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f284,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f109,f114,f119,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f596,plain,
    ( ~ spl4_45
    | ~ spl4_1
    | ~ spl4_5
    | spl4_11 ),
    inference(avatar_split_clause,[],[f583,f163,f112,f92,f593])).

fof(f163,plain,
    ( spl4_11
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f583,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_11 ),
    inference(forward_demodulation,[],[f165,f176])).

fof(f165,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f582,plain,
    ( k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | sK0 != k1_relset_1(sK0,sK1,sK3)
    | sK3 != k7_relat_1(sK3,k1_relat_1(sK3))
    | v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f581,plain,
    ( ~ spl4_43
    | ~ spl4_1
    | ~ spl4_5
    | spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f572,f213,f163,f112,f92,f578])).

fof(f578,plain,
    ( spl4_43
  <=> v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f213,plain,
    ( spl4_16
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f572,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_11
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f571,f176])).

fof(f571,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1)
    | spl4_11
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f165,f215])).

fof(f215,plain,
    ( sK0 = sK2
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f554,plain,
    ( k1_xboole_0 != sK3
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f481,plain,
    ( spl4_36
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f187,f172,f478])).

fof(f478,plain,
    ( spl4_36
  <=> sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f187,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f84,f174,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f412,plain,
    ( spl4_32
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f384,f365,f409])).

fof(f409,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f365,plain,
    ( spl4_28
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f384,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f367,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f367,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f365])).

fof(f368,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f305,f299,f102,f365])).

fof(f102,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f299,plain,
    ( spl4_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f305,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f104,f301,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f301,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f299])).

fof(f104,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f326,plain,
    ( spl4_25
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f112,f323])).

fof(f323,plain,
    ( spl4_25
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f158,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f114,f73])).

fof(f302,plain,
    ( spl4_24
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f248,f121,f112,f299])).

fof(f121,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f248,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f114,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f257,plain,
    ( ~ spl4_7
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl4_7
    | spl4_17 ),
    inference(subsumption_resolution,[],[f251,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f251,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_7
    | spl4_17 ),
    inference(superposition,[],[f219,f123])).

fof(f219,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_17
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f220,plain,
    ( spl4_16
    | ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f151,f97,f217,f213])).

fof(f151,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f99])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f175,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f143,f112,f172])).

fof(f143,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f114,f72])).

fof(f170,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f161,f112,f92,f167,f163])).

fof(f161,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f54,f160])).

fof(f160,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f94,f114,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f129,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f56,f126])).

fof(f126,plain,
    ( spl4_8
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f124,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f53,f121,f117])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f51,f112])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f50,f107])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f100,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f49,f92])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:26:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (5029)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (5031)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (5028)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (5023)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (5046)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (5038)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (5043)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (5041)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (5026)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (5030)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.56  % (5032)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (5044)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.57  % (5037)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.50/0.57  % (5024)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.57  % (5034)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.50/0.57  % (5045)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.50/0.58  % (5036)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.76/0.59  % (5025)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.76/0.60  % (5027)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.76/0.60  % (5047)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.76/0.60  % (5046)Refutation found. Thanks to Tanya!
% 1.76/0.60  % SZS status Theorem for theBenchmark
% 1.76/0.60  % SZS output start Proof for theBenchmark
% 1.76/0.60  fof(f801,plain,(
% 1.76/0.60    $false),
% 1.76/0.60    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f124,f129,f170,f175,f220,f257,f302,f326,f368,f412,f481,f554,f581,f582,f596,f647,f671,f677,f705,f709,f710,f796,f799])).
% 1.76/0.60  fof(f799,plain,(
% 1.76/0.60    ~spl4_1 | ~spl4_5 | spl4_12 | ~spl4_46),
% 1.76/0.60    inference(avatar_contradiction_clause,[],[f798])).
% 1.76/0.60  fof(f798,plain,(
% 1.76/0.60    $false | (~spl4_1 | ~spl4_5 | spl4_12 | ~spl4_46)),
% 1.76/0.60    inference(subsumption_resolution,[],[f600,f712])).
% 1.76/0.60  fof(f712,plain,(
% 1.76/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_5 | spl4_12)),
% 1.76/0.60    inference(forward_demodulation,[],[f169,f176])).
% 1.76/0.60  fof(f176,plain,(
% 1.76/0.60    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f94,f114,f81])).
% 1.76/0.60  fof(f81,plain,(
% 1.76/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f40])).
% 1.76/0.60  fof(f40,plain,(
% 1.76/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.76/0.60    inference(flattening,[],[f39])).
% 1.76/0.60  fof(f39,plain,(
% 1.76/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.76/0.60    inference(ennf_transformation,[],[f16])).
% 1.76/0.60  fof(f16,axiom,(
% 1.76/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.76/0.60  fof(f114,plain,(
% 1.76/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 1.76/0.60    inference(avatar_component_clause,[],[f112])).
% 1.76/0.60  fof(f112,plain,(
% 1.76/0.60    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.76/0.60  fof(f94,plain,(
% 1.76/0.60    v1_funct_1(sK3) | ~spl4_1),
% 1.76/0.60    inference(avatar_component_clause,[],[f92])).
% 1.76/0.60  fof(f92,plain,(
% 1.76/0.60    spl4_1 <=> v1_funct_1(sK3)),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.76/0.60  fof(f169,plain,(
% 1.76/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_12),
% 1.76/0.60    inference(avatar_component_clause,[],[f167])).
% 1.76/0.60  fof(f167,plain,(
% 1.76/0.60    spl4_12 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.76/0.60  fof(f600,plain,(
% 1.76/0.60    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_46),
% 1.76/0.60    inference(avatar_component_clause,[],[f598])).
% 1.76/0.60  fof(f598,plain,(
% 1.76/0.60    spl4_46 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.76/0.60  fof(f796,plain,(
% 1.76/0.60    ~spl4_1 | ~spl4_5 | spl4_46 | ~spl4_51),
% 1.76/0.60    inference(avatar_contradiction_clause,[],[f795])).
% 1.76/0.60  fof(f795,plain,(
% 1.76/0.60    $false | (~spl4_1 | ~spl4_5 | spl4_46 | ~spl4_51)),
% 1.76/0.60    inference(subsumption_resolution,[],[f794,f84])).
% 1.76/0.60  fof(f84,plain,(
% 1.76/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.76/0.60    inference(equality_resolution,[],[f69])).
% 1.76/0.60  fof(f69,plain,(
% 1.76/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.76/0.60    inference(cnf_transformation,[],[f47])).
% 1.76/0.60  fof(f47,plain,(
% 1.76/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.60    inference(flattening,[],[f46])).
% 1.76/0.60  fof(f46,plain,(
% 1.76/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.60    inference(nnf_transformation,[],[f3])).
% 1.76/0.60  fof(f3,axiom,(
% 1.76/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.60  fof(f794,plain,(
% 1.76/0.60    ~r1_tarski(sK2,sK2) | (~spl4_1 | ~spl4_5 | spl4_46 | ~spl4_51)),
% 1.76/0.60    inference(forward_demodulation,[],[f788,f703])).
% 1.76/0.60  fof(f703,plain,(
% 1.76/0.60    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_51),
% 1.76/0.60    inference(avatar_component_clause,[],[f702])).
% 1.76/0.60  fof(f702,plain,(
% 1.76/0.60    spl4_51 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.76/0.60  fof(f788,plain,(
% 1.76/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | (~spl4_1 | ~spl4_5 | spl4_46)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f333,f599,f465,f71])).
% 1.76/0.60  fof(f71,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.60    inference(cnf_transformation,[],[f33])).
% 1.76/0.60  fof(f33,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.76/0.60    inference(flattening,[],[f32])).
% 1.76/0.60  fof(f32,plain,(
% 1.76/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.76/0.60    inference(ennf_transformation,[],[f13])).
% 1.76/0.60  fof(f13,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.76/0.60  fof(f465,plain,(
% 1.76/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f333,f335,f62])).
% 1.76/0.60  fof(f62,plain,(
% 1.76/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f45])).
% 1.76/0.60  fof(f45,plain,(
% 1.76/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.76/0.60    inference(nnf_transformation,[],[f28])).
% 1.76/0.60  fof(f28,plain,(
% 1.76/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.76/0.60    inference(ennf_transformation,[],[f5])).
% 1.76/0.60  fof(f5,axiom,(
% 1.76/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.76/0.60  fof(f335,plain,(
% 1.76/0.60    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK1)) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f180,f74])).
% 1.76/0.60  fof(f74,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f36])).
% 1.76/0.60  fof(f36,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.60    inference(ennf_transformation,[],[f20])).
% 1.76/0.60  fof(f20,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.76/0.60    inference(pure_predicate_removal,[],[f10])).
% 1.76/0.60  fof(f10,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.76/0.60  fof(f180,plain,(
% 1.76/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.60    inference(forward_demodulation,[],[f178,f176])).
% 1.76/0.60  fof(f178,plain,(
% 1.76/0.60    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f94,f114,f83])).
% 1.76/0.60  fof(f83,plain,(
% 1.76/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f42])).
% 1.76/0.60  fof(f42,plain,(
% 1.76/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.76/0.60    inference(flattening,[],[f41])).
% 1.76/0.60  fof(f41,plain,(
% 1.76/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.76/0.60    inference(ennf_transformation,[],[f15])).
% 1.76/0.60  fof(f15,axiom,(
% 1.76/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.76/0.60  fof(f599,plain,(
% 1.76/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_46),
% 1.76/0.60    inference(avatar_component_clause,[],[f598])).
% 1.76/0.60  fof(f333,plain,(
% 1.76/0.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f180,f72])).
% 1.76/0.60  fof(f72,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f34])).
% 1.76/0.60  fof(f34,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.60    inference(ennf_transformation,[],[f9])).
% 1.76/0.60  fof(f9,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.76/0.60  fof(f710,plain,(
% 1.76/0.60    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | sK0 = k1_relat_1(sK3)),
% 1.76/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.76/0.60  fof(f709,plain,(
% 1.76/0.60    ~spl4_2 | ~spl4_13 | ~spl4_42 | spl4_51),
% 1.76/0.60    inference(avatar_contradiction_clause,[],[f708])).
% 1.76/0.60  fof(f708,plain,(
% 1.76/0.60    $false | (~spl4_2 | ~spl4_13 | ~spl4_42 | spl4_51)),
% 1.76/0.60    inference(subsumption_resolution,[],[f707,f99])).
% 1.76/0.60  fof(f99,plain,(
% 1.76/0.60    r1_tarski(sK2,sK0) | ~spl4_2),
% 1.76/0.60    inference(avatar_component_clause,[],[f97])).
% 1.76/0.60  fof(f97,plain,(
% 1.76/0.60    spl4_2 <=> r1_tarski(sK2,sK0)),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.76/0.60  fof(f707,plain,(
% 1.76/0.60    ~r1_tarski(sK2,sK0) | (~spl4_13 | ~spl4_42 | spl4_51)),
% 1.76/0.60    inference(forward_demodulation,[],[f706,f564])).
% 1.76/0.60  fof(f564,plain,(
% 1.76/0.60    sK0 = k1_relat_1(sK3) | ~spl4_42),
% 1.76/0.60    inference(avatar_component_clause,[],[f562])).
% 1.76/0.60  fof(f562,plain,(
% 1.76/0.60    spl4_42 <=> sK0 = k1_relat_1(sK3)),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.76/0.60  fof(f706,plain,(
% 1.76/0.60    ~r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_13 | spl4_51)),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f174,f704,f60])).
% 1.76/0.60  fof(f60,plain,(
% 1.76/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.76/0.60    inference(cnf_transformation,[],[f25])).
% 1.76/0.60  fof(f25,plain,(
% 1.76/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.76/0.60    inference(flattening,[],[f24])).
% 1.76/0.60  % (5035)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.76/0.60  fof(f24,plain,(
% 1.76/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.76/0.60    inference(ennf_transformation,[],[f7])).
% 1.76/0.60  fof(f7,axiom,(
% 1.76/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.76/0.60  fof(f704,plain,(
% 1.76/0.60    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_51),
% 1.76/0.60    inference(avatar_component_clause,[],[f702])).
% 1.76/0.60  fof(f174,plain,(
% 1.76/0.60    v1_relat_1(sK3) | ~spl4_13),
% 1.76/0.60    inference(avatar_component_clause,[],[f172])).
% 1.76/0.60  fof(f172,plain,(
% 1.76/0.60    spl4_13 <=> v1_relat_1(sK3)),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.76/0.60  fof(f705,plain,(
% 1.76/0.60    ~spl4_51 | spl4_49 | ~spl4_50),
% 1.76/0.60    inference(avatar_split_clause,[],[f678,f674,f668,f702])).
% 1.76/0.60  fof(f668,plain,(
% 1.76/0.60    spl4_49 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.76/0.60  fof(f674,plain,(
% 1.76/0.60    spl4_50 <=> k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.76/0.60  fof(f678,plain,(
% 1.76/0.60    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_49 | ~spl4_50)),
% 1.76/0.60    inference(superposition,[],[f670,f676])).
% 1.76/0.60  fof(f676,plain,(
% 1.76/0.60    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_50),
% 1.76/0.60    inference(avatar_component_clause,[],[f674])).
% 1.76/0.60  fof(f670,plain,(
% 1.76/0.60    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_49),
% 1.76/0.60    inference(avatar_component_clause,[],[f668])).
% 1.76/0.60  fof(f677,plain,(
% 1.76/0.60    spl4_50 | ~spl4_46),
% 1.76/0.60    inference(avatar_split_clause,[],[f603,f598,f674])).
% 1.76/0.60  fof(f603,plain,(
% 1.76/0.60    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_46),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f600,f73])).
% 1.76/0.60  fof(f73,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f35])).
% 1.76/0.60  fof(f35,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.60    inference(ennf_transformation,[],[f12])).
% 1.76/0.61  fof(f12,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.76/0.61  fof(f671,plain,(
% 1.76/0.61    ~spl4_49 | spl4_6 | spl4_45 | ~spl4_46),
% 1.76/0.61    inference(avatar_split_clause,[],[f605,f598,f593,f117,f668])).
% 1.76/0.61  fof(f117,plain,(
% 1.76/0.61    spl4_6 <=> k1_xboole_0 = sK1),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.76/0.61  fof(f593,plain,(
% 1.76/0.61    spl4_45 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.76/0.61  fof(f605,plain,(
% 1.76/0.61    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (spl4_6 | spl4_45 | ~spl4_46)),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f119,f595,f600,f77])).
% 1.76/0.61  fof(f77,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f48])).
% 1.76/0.61  fof(f48,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(nnf_transformation,[],[f38])).
% 1.76/0.61  fof(f38,plain,(
% 1.76/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(flattening,[],[f37])).
% 1.76/0.61  fof(f37,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(ennf_transformation,[],[f14])).
% 1.76/0.61  fof(f14,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.76/0.61  fof(f595,plain,(
% 1.76/0.61    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_45),
% 1.76/0.61    inference(avatar_component_clause,[],[f593])).
% 1.76/0.61  fof(f119,plain,(
% 1.76/0.61    k1_xboole_0 != sK1 | spl4_6),
% 1.76/0.61    inference(avatar_component_clause,[],[f117])).
% 1.76/0.61  fof(f647,plain,(
% 1.76/0.61    spl4_18 | ~spl4_4 | ~spl4_5 | spl4_6),
% 1.76/0.61    inference(avatar_split_clause,[],[f284,f117,f112,f107,f222])).
% 1.76/0.61  fof(f222,plain,(
% 1.76/0.61    spl4_18 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.76/0.61  fof(f107,plain,(
% 1.76/0.61    spl4_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.76/0.61  fof(f284,plain,(
% 1.76/0.61    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_4 | ~spl4_5 | spl4_6)),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f109,f114,f119,f75])).
% 1.76/0.61  fof(f75,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f48])).
% 1.76/0.61  fof(f109,plain,(
% 1.76/0.61    v1_funct_2(sK3,sK0,sK1) | ~spl4_4),
% 1.76/0.61    inference(avatar_component_clause,[],[f107])).
% 1.76/0.61  fof(f596,plain,(
% 1.76/0.61    ~spl4_45 | ~spl4_1 | ~spl4_5 | spl4_11),
% 1.76/0.61    inference(avatar_split_clause,[],[f583,f163,f112,f92,f593])).
% 1.76/0.61  fof(f163,plain,(
% 1.76/0.61    spl4_11 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.76/0.61  fof(f583,plain,(
% 1.76/0.61    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_5 | spl4_11)),
% 1.76/0.61    inference(forward_demodulation,[],[f165,f176])).
% 1.76/0.61  fof(f165,plain,(
% 1.76/0.61    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_11),
% 1.76/0.61    inference(avatar_component_clause,[],[f163])).
% 1.76/0.61  fof(f582,plain,(
% 1.76/0.61    k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | sK0 != k1_relset_1(sK0,sK1,sK3) | sK3 != k7_relat_1(sK3,k1_relat_1(sK3)) | v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 1.76/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.76/0.61  fof(f581,plain,(
% 1.76/0.61    ~spl4_43 | ~spl4_1 | ~spl4_5 | spl4_11 | ~spl4_16),
% 1.76/0.61    inference(avatar_split_clause,[],[f572,f213,f163,f112,f92,f578])).
% 1.76/0.61  fof(f578,plain,(
% 1.76/0.61    spl4_43 <=> v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.76/0.61  fof(f213,plain,(
% 1.76/0.61    spl4_16 <=> sK0 = sK2),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.76/0.61  fof(f572,plain,(
% 1.76/0.61    ~v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1) | (~spl4_1 | ~spl4_5 | spl4_11 | ~spl4_16)),
% 1.76/0.61    inference(forward_demodulation,[],[f571,f176])).
% 1.76/0.61  fof(f571,plain,(
% 1.76/0.61    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1) | (spl4_11 | ~spl4_16)),
% 1.76/0.61    inference(forward_demodulation,[],[f165,f215])).
% 1.76/0.61  fof(f215,plain,(
% 1.76/0.61    sK0 = sK2 | ~spl4_16),
% 1.76/0.61    inference(avatar_component_clause,[],[f213])).
% 1.76/0.61  fof(f554,plain,(
% 1.76/0.61    k1_xboole_0 != sK3 | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.76/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.76/0.61  fof(f481,plain,(
% 1.76/0.61    spl4_36 | ~spl4_13),
% 1.76/0.61    inference(avatar_split_clause,[],[f187,f172,f478])).
% 1.76/0.61  fof(f478,plain,(
% 1.76/0.61    spl4_36 <=> sK3 = k7_relat_1(sK3,k1_relat_1(sK3))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.76/0.61  fof(f187,plain,(
% 1.76/0.61    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) | ~spl4_13),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f84,f174,f61])).
% 1.76/0.61  fof(f61,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.76/0.61    inference(cnf_transformation,[],[f27])).
% 1.76/0.61  fof(f27,plain,(
% 1.76/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.76/0.61    inference(flattening,[],[f26])).
% 1.76/0.61  fof(f26,plain,(
% 1.76/0.61    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.76/0.61    inference(ennf_transformation,[],[f8])).
% 1.76/0.61  fof(f8,axiom,(
% 1.76/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.76/0.61  fof(f412,plain,(
% 1.76/0.61    spl4_32 | ~spl4_28),
% 1.76/0.61    inference(avatar_split_clause,[],[f384,f365,f409])).
% 1.76/0.61  fof(f409,plain,(
% 1.76/0.61    spl4_32 <=> k1_xboole_0 = sK3),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.76/0.61  fof(f365,plain,(
% 1.76/0.61    spl4_28 <=> v1_xboole_0(sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.76/0.61  fof(f384,plain,(
% 1.76/0.61    k1_xboole_0 = sK3 | ~spl4_28),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f367,f59])).
% 1.76/0.61  fof(f59,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f23])).
% 1.76/0.61  fof(f23,plain,(
% 1.76/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f2])).
% 1.76/0.61  fof(f2,axiom,(
% 1.76/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.76/0.61  fof(f367,plain,(
% 1.76/0.61    v1_xboole_0(sK3) | ~spl4_28),
% 1.76/0.61    inference(avatar_component_clause,[],[f365])).
% 1.76/0.61  fof(f368,plain,(
% 1.76/0.61    spl4_28 | ~spl4_3 | ~spl4_24),
% 1.76/0.61    inference(avatar_split_clause,[],[f305,f299,f102,f365])).
% 1.76/0.61  fof(f102,plain,(
% 1.76/0.61    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.76/0.61  fof(f299,plain,(
% 1.76/0.61    spl4_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.76/0.61  fof(f305,plain,(
% 1.76/0.61    v1_xboole_0(sK3) | (~spl4_3 | ~spl4_24)),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f104,f301,f64])).
% 1.76/0.61  fof(f64,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f29])).
% 1.76/0.61  fof(f29,plain,(
% 1.76/0.61    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f11])).
% 1.76/0.61  fof(f11,axiom,(
% 1.76/0.61    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.76/0.61  fof(f301,plain,(
% 1.76/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_24),
% 1.76/0.61    inference(avatar_component_clause,[],[f299])).
% 1.76/0.61  fof(f104,plain,(
% 1.76/0.61    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 1.76/0.61    inference(avatar_component_clause,[],[f102])).
% 1.76/0.61  fof(f326,plain,(
% 1.76/0.61    spl4_25 | ~spl4_5),
% 1.76/0.61    inference(avatar_split_clause,[],[f158,f112,f323])).
% 1.76/0.61  fof(f323,plain,(
% 1.76/0.61    spl4_25 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.76/0.61  fof(f158,plain,(
% 1.76/0.61    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_5),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f114,f73])).
% 1.76/0.61  fof(f302,plain,(
% 1.76/0.61    spl4_24 | ~spl4_5 | ~spl4_7),
% 1.76/0.61    inference(avatar_split_clause,[],[f248,f121,f112,f299])).
% 1.76/0.61  fof(f121,plain,(
% 1.76/0.61    spl4_7 <=> k1_xboole_0 = sK0),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.76/0.61  fof(f248,plain,(
% 1.76/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_5 | ~spl4_7)),
% 1.76/0.61    inference(superposition,[],[f114,f123])).
% 1.76/0.61  fof(f123,plain,(
% 1.76/0.61    k1_xboole_0 = sK0 | ~spl4_7),
% 1.76/0.61    inference(avatar_component_clause,[],[f121])).
% 1.76/0.61  fof(f257,plain,(
% 1.76/0.61    ~spl4_7 | spl4_17),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f256])).
% 1.76/0.61  fof(f256,plain,(
% 1.76/0.61    $false | (~spl4_7 | spl4_17)),
% 1.76/0.61    inference(subsumption_resolution,[],[f251,f58])).
% 1.76/0.61  fof(f58,plain,(
% 1.76/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f4])).
% 1.76/0.61  fof(f4,axiom,(
% 1.76/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.76/0.61  fof(f251,plain,(
% 1.76/0.61    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_7 | spl4_17)),
% 1.76/0.61    inference(superposition,[],[f219,f123])).
% 1.76/0.61  fof(f219,plain,(
% 1.76/0.61    ~r1_tarski(sK0,sK2) | spl4_17),
% 1.76/0.61    inference(avatar_component_clause,[],[f217])).
% 1.76/0.61  fof(f217,plain,(
% 1.76/0.61    spl4_17 <=> r1_tarski(sK0,sK2)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.76/0.61  fof(f220,plain,(
% 1.76/0.61    spl4_16 | ~spl4_17 | ~spl4_2),
% 1.76/0.61    inference(avatar_split_clause,[],[f151,f97,f217,f213])).
% 1.76/0.61  fof(f151,plain,(
% 1.76/0.61    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_2),
% 1.76/0.61    inference(resolution,[],[f70,f99])).
% 1.76/0.61  fof(f70,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.76/0.61    inference(cnf_transformation,[],[f47])).
% 1.76/0.61  fof(f175,plain,(
% 1.76/0.61    spl4_13 | ~spl4_5),
% 1.76/0.61    inference(avatar_split_clause,[],[f143,f112,f172])).
% 1.76/0.61  fof(f143,plain,(
% 1.76/0.61    v1_relat_1(sK3) | ~spl4_5),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f114,f72])).
% 1.76/0.61  fof(f170,plain,(
% 1.76/0.61    ~spl4_11 | ~spl4_12 | ~spl4_1 | ~spl4_5),
% 1.76/0.61    inference(avatar_split_clause,[],[f161,f112,f92,f167,f163])).
% 1.76/0.61  fof(f161,plain,(
% 1.76/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_5)),
% 1.76/0.61    inference(subsumption_resolution,[],[f54,f160])).
% 1.76/0.61  fof(f160,plain,(
% 1.76/0.61    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | (~spl4_1 | ~spl4_5)),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f94,f114,f82])).
% 1.76/0.61  fof(f82,plain,(
% 1.76/0.61    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f42])).
% 1.76/0.61  fof(f54,plain,(
% 1.76/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f44,plain,(
% 1.76/0.61    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f43])).
% 1.76/0.61  fof(f43,plain,(
% 1.76/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f22,plain,(
% 1.76/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.76/0.61    inference(flattening,[],[f21])).
% 1.76/0.61  fof(f21,plain,(
% 1.76/0.61    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.76/0.61    inference(ennf_transformation,[],[f19])).
% 1.76/0.61  fof(f19,negated_conjecture,(
% 1.76/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.76/0.61    inference(negated_conjecture,[],[f18])).
% 1.76/0.61  fof(f18,conjecture,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.76/0.61  fof(f129,plain,(
% 1.76/0.61    spl4_8),
% 1.76/0.61    inference(avatar_split_clause,[],[f56,f126])).
% 1.76/0.61  fof(f126,plain,(
% 1.76/0.61    spl4_8 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.76/0.61  fof(f56,plain,(
% 1.76/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.76/0.61    inference(cnf_transformation,[],[f6])).
% 1.76/0.61  fof(f6,axiom,(
% 1.76/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.76/0.61  fof(f124,plain,(
% 1.76/0.61    ~spl4_6 | spl4_7),
% 1.76/0.61    inference(avatar_split_clause,[],[f53,f121,f117])).
% 1.76/0.61  fof(f53,plain,(
% 1.76/0.61    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f115,plain,(
% 1.76/0.61    spl4_5),
% 1.76/0.61    inference(avatar_split_clause,[],[f51,f112])).
% 1.76/0.61  fof(f51,plain,(
% 1.76/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f110,plain,(
% 1.76/0.61    spl4_4),
% 1.76/0.61    inference(avatar_split_clause,[],[f50,f107])).
% 1.76/0.61  fof(f50,plain,(
% 1.76/0.61    v1_funct_2(sK3,sK0,sK1)),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f105,plain,(
% 1.76/0.61    spl4_3),
% 1.76/0.61    inference(avatar_split_clause,[],[f55,f102])).
% 1.76/0.61  fof(f55,plain,(
% 1.76/0.61    v1_xboole_0(k1_xboole_0)),
% 1.76/0.61    inference(cnf_transformation,[],[f1])).
% 1.76/0.61  fof(f1,axiom,(
% 1.76/0.61    v1_xboole_0(k1_xboole_0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.76/0.61  fof(f100,plain,(
% 1.76/0.61    spl4_2),
% 1.76/0.61    inference(avatar_split_clause,[],[f52,f97])).
% 1.76/0.61  fof(f52,plain,(
% 1.76/0.61    r1_tarski(sK2,sK0)),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f95,plain,(
% 1.76/0.61    spl4_1),
% 1.76/0.61    inference(avatar_split_clause,[],[f49,f92])).
% 1.76/0.61  fof(f49,plain,(
% 1.76/0.61    v1_funct_1(sK3)),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  % SZS output end Proof for theBenchmark
% 1.76/0.61  % (5046)------------------------------
% 1.76/0.61  % (5046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (5046)Termination reason: Refutation
% 1.76/0.61  
% 1.76/0.61  % (5046)Memory used [KB]: 11129
% 1.76/0.61  % (5046)Time elapsed: 0.109 s
% 1.76/0.61  % (5046)------------------------------
% 1.76/0.61  % (5046)------------------------------
% 1.76/0.61  % (5022)Success in time 0.253 s
%------------------------------------------------------------------------------
