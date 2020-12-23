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
% DateTime   : Thu Dec  3 13:03:17 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 402 expanded)
%              Number of leaves         :   25 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  425 (1254 expanded)
%              Number of equality atoms :   64 ( 170 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f103,f114,f118,f139,f146,f155,f184,f723,f945,f1515,f1849,f2166])).

fof(f2166,plain,
    ( spl4_39
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f2052,f182,f137,f869])).

fof(f869,plain,
    ( spl4_39
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f137,plain,
    ( spl4_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f182,plain,
    ( spl4_14
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f2052,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(resolution,[],[f1657,f138])).

fof(f138,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f1657,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(X6)
        | sK2 = k1_relat_1(k7_relat_1(X6,sK2)) )
    | ~ spl4_14 ),
    inference(resolution,[],[f268,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f268,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f267,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(sK2,X0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f183,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f183,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1849,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_10
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f1848])).

fof(f1848,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | spl4_10
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1841,f1382])).

fof(f1382,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(superposition,[],[f956,f870])).

fof(f870,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f869])).

fof(f956,plain,
    ( ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f955,f322])).

fof(f322,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f309,f132])).

fof(f132,plain,
    ( ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f122,f92])).

fof(f92,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f122,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f309,plain,
    ( ! [X6] : v1_relat_1(k2_partfun1(sK0,sK1,sK3,X6))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f131,plain,
    ( ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f121,f92])).

fof(f121,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f955,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f949,f304])).

fof(f304,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f129,f132])).

fof(f129,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f120,f92])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f949,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f897,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f897,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f827,f322])).

fof(f827,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f330,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f330,plain,
    ( ! [X10] : v5_relat_1(k7_relat_1(sK3,X10),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f313,f132])).

fof(f313,plain,
    ( ! [X10] : v5_relat_1(k2_partfun1(sK0,sK1,sK3,X10),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1841,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | spl4_10 ),
    inference(superposition,[],[f145,f1557])).

fof(f1557,plain,
    ( ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f962,f92])).

fof(f962,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f55])).

fof(f145,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_10
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1515,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_11
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f1514])).

fof(f1514,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | spl4_11
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1506,f154])).

fof(f154,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_11
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1506,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(superposition,[],[f958,f870])).

fof(f958,plain,
    ( ! [X2] : m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f957,f322])).

fof(f957,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f950,f304])).

fof(f950,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f897,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f945,plain,
    ( spl4_39
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f872,f163,f137,f95,f869])).

fof(f95,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f163,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f872,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(resolution,[],[f96,f726])).

fof(f726,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f725,f138])).

fof(f725,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK3)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_13 ),
    inference(superposition,[],[f60,f164])).

fof(f164,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f96,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f723,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f135,f116,f112,f101,f163])).

fof(f101,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f135,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f126,f134])).

fof(f134,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f133,f102])).

fof(f102,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f133,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f125,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f126,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f184,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f171,f109,f95,f182])).

fof(f109,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f171,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f96,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f155,plain,
    ( ~ spl4_11
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(avatar_split_clause,[],[f147,f141,f116,f91,f153])).

fof(f141,plain,
    ( spl4_9
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f147,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(forward_demodulation,[],[f142,f132])).

fof(f142,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f146,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f130,f116,f91,f144,f141])).

fof(f130,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f47,f129])).

fof(f47,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f139,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f123,f116,f137])).

fof(f123,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f69])).

fof(f118,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f51,f116])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f48,f112,f109])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f50,f101])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (23163)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (23155)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (23174)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (23158)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (23156)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (23157)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (23169)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (23160)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (23159)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (23161)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (23154)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (23172)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (23168)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (23171)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (23165)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (23164)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (23167)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (23162)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (23166)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (23173)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (23170)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.70/0.61  % (23154)Refutation found. Thanks to Tanya!
% 1.70/0.61  % SZS status Theorem for theBenchmark
% 1.70/0.61  % SZS output start Proof for theBenchmark
% 1.70/0.61  fof(f2167,plain,(
% 1.70/0.61    $false),
% 1.70/0.61    inference(avatar_sat_refutation,[],[f93,f97,f103,f114,f118,f139,f146,f155,f184,f723,f945,f1515,f1849,f2166])).
% 1.70/0.61  fof(f2166,plain,(
% 1.70/0.61    spl4_39 | ~spl4_8 | ~spl4_14),
% 1.70/0.61    inference(avatar_split_clause,[],[f2052,f182,f137,f869])).
% 1.70/0.61  fof(f869,plain,(
% 1.70/0.61    spl4_39 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.70/0.61  fof(f137,plain,(
% 1.70/0.61    spl4_8 <=> v1_relat_1(sK3)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.70/0.61  fof(f182,plain,(
% 1.70/0.61    spl4_14 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.70/0.61  fof(f2052,plain,(
% 1.70/0.61    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_8 | ~spl4_14)),
% 1.70/0.61    inference(resolution,[],[f1657,f138])).
% 1.70/0.61  fof(f138,plain,(
% 1.70/0.61    v1_relat_1(sK3) | ~spl4_8),
% 1.70/0.61    inference(avatar_component_clause,[],[f137])).
% 1.70/0.61  fof(f1657,plain,(
% 1.70/0.61    ( ! [X6] : (~v1_relat_1(X6) | sK2 = k1_relat_1(k7_relat_1(X6,sK2))) ) | ~spl4_14),
% 1.70/0.61    inference(resolution,[],[f268,f60])).
% 1.70/0.61  fof(f60,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.70/0.61    inference(cnf_transformation,[],[f34])).
% 1.70/0.61  fof(f34,plain,(
% 1.70/0.61    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.70/0.61    inference(flattening,[],[f33])).
% 1.70/0.61  fof(f33,plain,(
% 1.70/0.61    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.70/0.61    inference(ennf_transformation,[],[f12])).
% 1.70/0.61  fof(f12,axiom,(
% 1.70/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.70/0.61  fof(f268,plain,(
% 1.70/0.61    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl4_14),
% 1.70/0.61    inference(subsumption_resolution,[],[f267,f63])).
% 1.70/0.61  fof(f63,plain,(
% 1.70/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f3])).
% 1.70/0.61  fof(f3,axiom,(
% 1.70/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.70/0.61  fof(f267,plain,(
% 1.70/0.61    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(sK2,X0)) ) | ~spl4_14),
% 1.70/0.61    inference(resolution,[],[f183,f66])).
% 1.70/0.61  fof(f66,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f37])).
% 1.70/0.61  fof(f37,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.70/0.61    inference(flattening,[],[f36])).
% 1.70/0.61  fof(f36,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.70/0.61    inference(ennf_transformation,[],[f2])).
% 1.70/0.61  fof(f2,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.70/0.61  fof(f183,plain,(
% 1.70/0.61    r1_tarski(sK2,k1_xboole_0) | ~spl4_14),
% 1.70/0.61    inference(avatar_component_clause,[],[f182])).
% 1.70/0.61  fof(f1849,plain,(
% 1.70/0.61    ~spl4_1 | ~spl4_7 | spl4_10 | ~spl4_39),
% 1.70/0.61    inference(avatar_contradiction_clause,[],[f1848])).
% 1.70/0.61  fof(f1848,plain,(
% 1.70/0.61    $false | (~spl4_1 | ~spl4_7 | spl4_10 | ~spl4_39)),
% 1.70/0.61    inference(subsumption_resolution,[],[f1841,f1382])).
% 1.70/0.61  fof(f1382,plain,(
% 1.70/0.61    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_7 | ~spl4_39)),
% 1.70/0.61    inference(superposition,[],[f956,f870])).
% 1.70/0.61  fof(f870,plain,(
% 1.70/0.61    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_39),
% 1.70/0.61    inference(avatar_component_clause,[],[f869])).
% 1.70/0.61  fof(f956,plain,(
% 1.70/0.61    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f955,f322])).
% 1.70/0.61  fof(f322,plain,(
% 1.70/0.61    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(forward_demodulation,[],[f309,f132])).
% 1.70/0.61  fof(f132,plain,(
% 1.70/0.61    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f122,f92])).
% 1.70/0.61  fof(f92,plain,(
% 1.70/0.61    v1_funct_1(sK3) | ~spl4_1),
% 1.70/0.61    inference(avatar_component_clause,[],[f91])).
% 1.70/0.61  fof(f91,plain,(
% 1.70/0.61    spl4_1 <=> v1_funct_1(sK3)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.70/0.61  fof(f122,plain,(
% 1.70/0.61    ( ! [X2] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_7),
% 1.70/0.61    inference(resolution,[],[f117,f55])).
% 1.70/0.61  fof(f55,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f30])).
% 1.70/0.61  fof(f30,plain,(
% 1.70/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.61    inference(flattening,[],[f29])).
% 1.70/0.61  fof(f29,plain,(
% 1.70/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.61    inference(ennf_transformation,[],[f20])).
% 1.70/0.61  fof(f20,axiom,(
% 1.70/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.70/0.61  fof(f117,plain,(
% 1.70/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.70/0.61    inference(avatar_component_clause,[],[f116])).
% 1.70/0.61  fof(f116,plain,(
% 1.70/0.61    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.70/0.61  fof(f309,plain,(
% 1.70/0.61    ( ! [X6] : (v1_relat_1(k2_partfun1(sK0,sK1,sK3,X6))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(resolution,[],[f131,f69])).
% 1.70/0.61  fof(f69,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f38])).
% 1.70/0.61  fof(f38,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.61    inference(ennf_transformation,[],[f15])).
% 1.70/0.61  fof(f15,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.70/0.61  fof(f131,plain,(
% 1.70/0.61    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f121,f92])).
% 1.70/0.61  fof(f121,plain,(
% 1.70/0.61    ( ! [X1] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_7),
% 1.70/0.61    inference(resolution,[],[f117,f54])).
% 1.70/0.61  fof(f54,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f28])).
% 1.70/0.61  fof(f28,plain,(
% 1.70/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.61    inference(flattening,[],[f27])).
% 1.70/0.61  fof(f27,plain,(
% 1.70/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.61    inference(ennf_transformation,[],[f19])).
% 1.70/0.61  fof(f19,axiom,(
% 1.70/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.70/0.61  fof(f955,plain,(
% 1.70/0.61    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f949,f304])).
% 1.70/0.61  fof(f304,plain,(
% 1.70/0.61    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(superposition,[],[f129,f132])).
% 1.70/0.61  fof(f129,plain,(
% 1.70/0.61    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f120,f92])).
% 1.70/0.61  fof(f120,plain,(
% 1.70/0.61    ( ! [X0] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | ~spl4_7),
% 1.70/0.61    inference(resolution,[],[f117,f53])).
% 1.70/0.61  fof(f53,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f28])).
% 1.70/0.61  fof(f949,plain,(
% 1.70/0.61    ( ! [X1] : (~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(resolution,[],[f897,f76])).
% 1.70/0.61  fof(f76,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f42])).
% 1.70/0.61  fof(f42,plain,(
% 1.70/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.70/0.61    inference(flattening,[],[f41])).
% 1.70/0.61  fof(f41,plain,(
% 1.70/0.61    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.70/0.61    inference(ennf_transformation,[],[f21])).
% 1.70/0.61  fof(f21,axiom,(
% 1.70/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.70/0.61  fof(f897,plain,(
% 1.70/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f827,f322])).
% 1.70/0.61  fof(f827,plain,(
% 1.70/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(resolution,[],[f330,f80])).
% 1.70/0.61  fof(f80,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f44])).
% 1.70/0.61  fof(f44,plain,(
% 1.70/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.70/0.61    inference(ennf_transformation,[],[f9])).
% 1.70/0.61  fof(f9,axiom,(
% 1.70/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.70/0.61  fof(f330,plain,(
% 1.70/0.61    ( ! [X10] : (v5_relat_1(k7_relat_1(sK3,X10),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(forward_demodulation,[],[f313,f132])).
% 1.70/0.61  fof(f313,plain,(
% 1.70/0.61    ( ! [X10] : (v5_relat_1(k2_partfun1(sK0,sK1,sK3,X10),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(resolution,[],[f131,f82])).
% 1.70/0.61  fof(f82,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f46])).
% 1.70/0.61  fof(f46,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.61    inference(ennf_transformation,[],[f24])).
% 1.70/0.61  fof(f24,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.70/0.61    inference(pure_predicate_removal,[],[f16])).
% 1.70/0.61  fof(f16,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.70/0.61  fof(f1841,plain,(
% 1.70/0.61    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_7 | spl4_10)),
% 1.70/0.61    inference(superposition,[],[f145,f1557])).
% 1.70/0.61  fof(f1557,plain,(
% 1.70/0.61    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f962,f92])).
% 1.70/0.61  fof(f962,plain,(
% 1.70/0.61    ( ! [X2] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_7),
% 1.70/0.61    inference(resolution,[],[f117,f55])).
% 1.70/0.61  fof(f145,plain,(
% 1.70/0.61    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_10),
% 1.70/0.61    inference(avatar_component_clause,[],[f144])).
% 1.70/0.61  fof(f144,plain,(
% 1.70/0.61    spl4_10 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.70/0.61  fof(f1515,plain,(
% 1.70/0.61    ~spl4_1 | ~spl4_7 | spl4_11 | ~spl4_39),
% 1.70/0.61    inference(avatar_contradiction_clause,[],[f1514])).
% 1.70/0.61  fof(f1514,plain,(
% 1.70/0.61    $false | (~spl4_1 | ~spl4_7 | spl4_11 | ~spl4_39)),
% 1.70/0.61    inference(subsumption_resolution,[],[f1506,f154])).
% 1.70/0.61  fof(f154,plain,(
% 1.70/0.61    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_11),
% 1.70/0.61    inference(avatar_component_clause,[],[f153])).
% 1.70/0.61  fof(f153,plain,(
% 1.70/0.61    spl4_11 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.70/0.61  fof(f1506,plain,(
% 1.70/0.61    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7 | ~spl4_39)),
% 1.70/0.61    inference(superposition,[],[f958,f870])).
% 1.70/0.61  fof(f958,plain,(
% 1.70/0.61    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f957,f322])).
% 1.70/0.61  fof(f957,plain,(
% 1.70/0.61    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f950,f304])).
% 1.70/0.61  fof(f950,plain,(
% 1.70/0.61    ( ! [X2] : (~v1_funct_1(k7_relat_1(sK3,X2)) | ~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 1.70/0.61    inference(resolution,[],[f897,f77])).
% 1.70/0.61  fof(f77,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f42])).
% 1.70/0.61  fof(f945,plain,(
% 1.70/0.61    spl4_39 | ~spl4_2 | ~spl4_8 | ~spl4_13),
% 1.70/0.61    inference(avatar_split_clause,[],[f872,f163,f137,f95,f869])).
% 1.70/0.62  fof(f95,plain,(
% 1.70/0.62    spl4_2 <=> r1_tarski(sK2,sK0)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.70/0.62  fof(f163,plain,(
% 1.70/0.62    spl4_13 <=> sK0 = k1_relat_1(sK3)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.70/0.62  fof(f872,plain,(
% 1.70/0.62    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_8 | ~spl4_13)),
% 1.70/0.62    inference(resolution,[],[f96,f726])).
% 1.70/0.62  fof(f726,plain,(
% 1.70/0.62    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_8 | ~spl4_13)),
% 1.70/0.62    inference(subsumption_resolution,[],[f725,f138])).
% 1.70/0.62  fof(f725,plain,(
% 1.70/0.62    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK3) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_13),
% 1.70/0.62    inference(superposition,[],[f60,f164])).
% 1.70/0.62  fof(f164,plain,(
% 1.70/0.62    sK0 = k1_relat_1(sK3) | ~spl4_13),
% 1.70/0.62    inference(avatar_component_clause,[],[f163])).
% 1.70/0.62  fof(f96,plain,(
% 1.70/0.62    r1_tarski(sK2,sK0) | ~spl4_2),
% 1.70/0.62    inference(avatar_component_clause,[],[f95])).
% 1.70/0.62  fof(f723,plain,(
% 1.70/0.62    spl4_13 | ~spl4_3 | spl4_6 | ~spl4_7),
% 1.70/0.62    inference(avatar_split_clause,[],[f135,f116,f112,f101,f163])).
% 1.70/0.62  fof(f101,plain,(
% 1.70/0.62    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.70/0.62  fof(f112,plain,(
% 1.70/0.62    spl4_6 <=> k1_xboole_0 = sK1),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.70/0.62  fof(f135,plain,(
% 1.70/0.62    sK0 = k1_relat_1(sK3) | (~spl4_3 | spl4_6 | ~spl4_7)),
% 1.70/0.62    inference(forward_demodulation,[],[f126,f134])).
% 1.70/0.62  fof(f134,plain,(
% 1.70/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | spl4_6 | ~spl4_7)),
% 1.70/0.62    inference(subsumption_resolution,[],[f133,f102])).
% 1.70/0.62  fof(f102,plain,(
% 1.70/0.62    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 1.70/0.62    inference(avatar_component_clause,[],[f101])).
% 1.70/0.62  fof(f133,plain,(
% 1.70/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl4_6 | ~spl4_7)),
% 1.70/0.62    inference(subsumption_resolution,[],[f125,f113])).
% 1.70/0.62  fof(f113,plain,(
% 1.70/0.62    k1_xboole_0 != sK1 | spl4_6),
% 1.70/0.62    inference(avatar_component_clause,[],[f112])).
% 1.70/0.62  fof(f125,plain,(
% 1.70/0.62    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl4_7),
% 1.70/0.62    inference(resolution,[],[f117,f75])).
% 1.70/0.62  fof(f75,plain,(
% 1.70/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f40])).
% 1.70/0.62  fof(f40,plain,(
% 1.70/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.62    inference(flattening,[],[f39])).
% 1.70/0.62  fof(f39,plain,(
% 1.70/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.62    inference(ennf_transformation,[],[f18])).
% 1.70/0.62  fof(f18,axiom,(
% 1.70/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.70/0.62  fof(f126,plain,(
% 1.70/0.62    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_7),
% 1.70/0.62    inference(resolution,[],[f117,f81])).
% 1.70/0.62  fof(f81,plain,(
% 1.70/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f45])).
% 1.70/0.62  fof(f45,plain,(
% 1.70/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.62    inference(ennf_transformation,[],[f17])).
% 1.70/0.62  fof(f17,axiom,(
% 1.70/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.70/0.62  fof(f184,plain,(
% 1.70/0.62    spl4_14 | ~spl4_2 | ~spl4_5),
% 1.70/0.62    inference(avatar_split_clause,[],[f171,f109,f95,f182])).
% 1.70/0.62  fof(f109,plain,(
% 1.70/0.62    spl4_5 <=> k1_xboole_0 = sK0),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.70/0.62  fof(f171,plain,(
% 1.70/0.62    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.70/0.62    inference(superposition,[],[f96,f110])).
% 1.70/0.62  fof(f110,plain,(
% 1.70/0.62    k1_xboole_0 = sK0 | ~spl4_5),
% 1.70/0.62    inference(avatar_component_clause,[],[f109])).
% 1.70/0.62  fof(f155,plain,(
% 1.70/0.62    ~spl4_11 | ~spl4_1 | ~spl4_7 | spl4_9),
% 1.70/0.62    inference(avatar_split_clause,[],[f147,f141,f116,f91,f153])).
% 1.70/0.62  fof(f141,plain,(
% 1.70/0.62    spl4_9 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.70/0.62  fof(f147,plain,(
% 1.70/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7 | spl4_9)),
% 1.70/0.62    inference(forward_demodulation,[],[f142,f132])).
% 1.70/0.62  fof(f142,plain,(
% 1.70/0.62    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_9),
% 1.70/0.62    inference(avatar_component_clause,[],[f141])).
% 1.70/0.62  fof(f146,plain,(
% 1.70/0.62    ~spl4_9 | ~spl4_10 | ~spl4_1 | ~spl4_7),
% 1.70/0.62    inference(avatar_split_clause,[],[f130,f116,f91,f144,f141])).
% 1.70/0.62  fof(f130,plain,(
% 1.70/0.62    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7)),
% 1.70/0.62    inference(subsumption_resolution,[],[f47,f129])).
% 1.70/0.62  fof(f47,plain,(
% 1.70/0.62    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.70/0.62    inference(cnf_transformation,[],[f26])).
% 1.70/0.62  fof(f26,plain,(
% 1.70/0.62    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.70/0.62    inference(flattening,[],[f25])).
% 1.70/0.62  fof(f25,plain,(
% 1.70/0.62    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.70/0.62    inference(ennf_transformation,[],[f23])).
% 1.70/0.62  fof(f23,negated_conjecture,(
% 1.70/0.62    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.70/0.62    inference(negated_conjecture,[],[f22])).
% 1.70/0.62  fof(f22,conjecture,(
% 1.70/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.70/0.62  fof(f139,plain,(
% 1.70/0.62    spl4_8 | ~spl4_7),
% 1.70/0.62    inference(avatar_split_clause,[],[f123,f116,f137])).
% 1.70/0.62  fof(f123,plain,(
% 1.70/0.62    v1_relat_1(sK3) | ~spl4_7),
% 1.70/0.62    inference(resolution,[],[f117,f69])).
% 1.70/0.62  fof(f118,plain,(
% 1.70/0.62    spl4_7),
% 1.70/0.62    inference(avatar_split_clause,[],[f51,f116])).
% 1.70/0.62  fof(f51,plain,(
% 1.70/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.70/0.62    inference(cnf_transformation,[],[f26])).
% 1.70/0.62  fof(f114,plain,(
% 1.70/0.62    spl4_5 | ~spl4_6),
% 1.70/0.62    inference(avatar_split_clause,[],[f48,f112,f109])).
% 1.70/0.62  fof(f48,plain,(
% 1.70/0.62    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.70/0.62    inference(cnf_transformation,[],[f26])).
% 1.70/0.62  fof(f103,plain,(
% 1.70/0.62    spl4_3),
% 1.70/0.62    inference(avatar_split_clause,[],[f50,f101])).
% 1.70/0.62  fof(f50,plain,(
% 1.70/0.62    v1_funct_2(sK3,sK0,sK1)),
% 1.70/0.62    inference(cnf_transformation,[],[f26])).
% 1.70/0.62  fof(f97,plain,(
% 1.70/0.62    spl4_2),
% 1.70/0.62    inference(avatar_split_clause,[],[f52,f95])).
% 1.70/0.62  fof(f52,plain,(
% 1.70/0.62    r1_tarski(sK2,sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f26])).
% 1.70/0.62  fof(f93,plain,(
% 1.70/0.62    spl4_1),
% 1.70/0.62    inference(avatar_split_clause,[],[f49,f91])).
% 1.70/0.62  fof(f49,plain,(
% 1.70/0.62    v1_funct_1(sK3)),
% 1.70/0.62    inference(cnf_transformation,[],[f26])).
% 1.70/0.62  % SZS output end Proof for theBenchmark
% 1.70/0.62  % (23154)------------------------------
% 1.70/0.62  % (23154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (23154)Termination reason: Refutation
% 1.70/0.62  
% 1.70/0.62  % (23154)Memory used [KB]: 7291
% 1.70/0.62  % (23154)Time elapsed: 0.181 s
% 1.70/0.62  % (23154)------------------------------
% 1.70/0.62  % (23154)------------------------------
% 1.70/0.62  % (23153)Success in time 0.255 s
%------------------------------------------------------------------------------
