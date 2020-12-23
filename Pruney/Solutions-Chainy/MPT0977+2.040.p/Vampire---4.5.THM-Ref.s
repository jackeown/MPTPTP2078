%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 173 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  298 ( 430 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f68,f76,f84,f91,f100,f117,f124,f129,f135,f150,f159,f165])).

fof(f165,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_7
    | spl3_13 ),
    inference(subsumption_resolution,[],[f163,f75])).

fof(f75,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f163,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_7
    | spl3_13 ),
    inference(subsumption_resolution,[],[f161,f90])).

fof(f90,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_7
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f161,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(resolution,[],[f158,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f158,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_13
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f159,plain,
    ( ~ spl3_13
    | ~ spl3_5
    | ~ spl3_8
    | spl3_12 ),
    inference(avatar_split_clause,[],[f154,f147,f97,f73,f156])).

fof(f97,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f147,plain,
    ( spl3_12
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f154,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_5
    | ~ spl3_8
    | spl3_12 ),
    inference(subsumption_resolution,[],[f153,f75])).

fof(f153,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_8
    | spl3_12 ),
    inference(subsumption_resolution,[],[f152,f99])).

fof(f99,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f152,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl3_12 ),
    inference(superposition,[],[f149,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f149,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f150,plain,
    ( ~ spl3_12
    | ~ spl3_3
    | spl3_11 ),
    inference(avatar_split_clause,[],[f145,f132,f59,f147])).

fof(f59,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f132,plain,
    ( spl3_11
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f145,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2)
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f144,f61])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f144,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_11 ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f143,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2)
    | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_11 ),
    inference(superposition,[],[f134,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f134,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( ~ spl3_11
    | spl3_2 ),
    inference(avatar_split_clause,[],[f130,f54,f132])).

fof(f54,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f130,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | spl3_2 ),
    inference(forward_demodulation,[],[f56,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f56,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f129,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_10 ),
    inference(subsumption_resolution,[],[f127,f75])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_8
    | spl3_10 ),
    inference(subsumption_resolution,[],[f126,f83])).

fof(f83,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_6
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f126,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_8
    | spl3_10 ),
    inference(subsumption_resolution,[],[f125,f99])).

fof(f125,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(superposition,[],[f123,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f123,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_10
  <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f124,plain,
    ( ~ spl3_10
    | ~ spl3_5
    | spl3_9 ),
    inference(avatar_split_clause,[],[f119,f114,f73,f121])).

fof(f114,plain,
    ( spl3_9
  <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f119,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | ~ spl3_5
    | spl3_9 ),
    inference(subsumption_resolution,[],[f118,f75])).

fof(f118,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(superposition,[],[f116,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f116,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( ~ spl3_9
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f112,f65,f59,f114])).

fof(f65,plain,
    ( spl3_4
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2)
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f111,f40])).

% (5398)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f111,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f110,f61])).

fof(f110,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_4 ),
    inference(superposition,[],[f67,f35])).

fof(f67,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f100,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f94,f59,f97])).

fof(f94,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f61])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f91,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f85,f59,f88])).

fof(f85,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f38,f61])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f84,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f78,f59,f81])).

fof(f78,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f37,f61])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f71,f59,f73])).

fof(f71,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f69,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f39,f61])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f68,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f63,f50,f65])).

fof(f50,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f52,f36])).

fof(f52,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f62,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).

fof(f27,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f57,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f32,f54,f50])).

fof(f32,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:56:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (5399)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (5417)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (5403)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (5401)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (5408)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (5400)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (5422)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (5412)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (5419)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (5412)Refutation not found, incomplete strategy% (5412)------------------------------
% 0.22/0.54  % (5412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5412)Memory used [KB]: 1791
% 0.22/0.54  % (5412)Time elapsed: 0.070 s
% 0.22/0.54  % (5412)------------------------------
% 0.22/0.54  % (5412)------------------------------
% 0.22/0.54  % (5419)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (5405)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f57,f62,f68,f76,f84,f91,f100,f117,f124,f129,f135,f150,f159,f165])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ~spl3_5 | ~spl3_7 | spl3_13),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    $false | (~spl3_5 | ~spl3_7 | spl3_13)),
% 0.22/0.54    inference(subsumption_resolution,[],[f163,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    spl3_5 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ~v1_relat_1(sK2) | (~spl3_7 | spl3_13)),
% 0.22/0.54    inference(subsumption_resolution,[],[f161,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    v5_relat_1(sK2,sK1) | ~spl3_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl3_7 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.54    inference(resolution,[],[f158,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f156])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    spl3_13 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ~spl3_13 | ~spl3_5 | ~spl3_8 | spl3_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f154,f147,f97,f73,f156])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    spl3_8 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    spl3_12 <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_5 | ~spl3_8 | spl3_12)),
% 0.22/0.54    inference(subsumption_resolution,[],[f153,f75])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | (~spl3_8 | spl3_12)),
% 0.22/0.54    inference(subsumption_resolution,[],[f152,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f97])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | spl3_12),
% 0.22/0.54    inference(superposition,[],[f149,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2) | spl3_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f147])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ~spl3_12 | ~spl3_3 | spl3_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f145,f132,f59,f147])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl3_11 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2) | (~spl3_3 | spl3_11)),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f59])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2) | ~m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_11),
% 0.22/0.54    inference(superposition,[],[f134,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) | spl3_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ~spl3_11 | spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f130,f54,f132])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    spl3_2 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) | spl3_2),
% 0.22/0.54    inference(forward_demodulation,[],[f56,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f54])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    $false | (~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f127,f75])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~v1_relat_1(sK2) | (~spl3_6 | ~spl3_8 | spl3_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f126,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    v4_relat_1(sK2,sK0) | ~spl3_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl3_6 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | (~spl3_8 | spl3_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f125,f99])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.54    inference(superposition,[],[f123,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f121])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl3_10 <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ~spl3_10 | ~spl3_5 | spl3_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f119,f114,f73,f121])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    spl3_9 <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | (~spl3_5 | spl3_9)),
% 0.22/0.54    inference(subsumption_resolution,[],[f118,f75])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(sK2) | spl3_9),
% 0.22/0.54    inference(superposition,[],[f116,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) | spl3_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f114])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ~spl3_9 | ~spl3_3 | spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f112,f65,f59,f114])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    spl3_4 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) | (~spl3_3 | spl3_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f111,f40])).
% 0.22/0.54  % (5398)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_3 | spl3_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f110,f61])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_4),
% 0.22/0.54    inference(superposition,[],[f67,f35])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) | spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f65])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl3_8 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f94,f59,f97])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f48,f61])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    spl3_7 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f85,f59,f88])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    v5_relat_1(sK2,sK1) | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f38,f61])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl3_6 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f78,f59,f81])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    v4_relat_1(sK2,sK0) | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f37,f61])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl3_5 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f71,f59,f73])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f69,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f39,f61])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~spl3_4 | spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f63,f50,f65])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    spl3_1 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) | spl3_1),
% 0.22/0.54    inference(backward_demodulation,[],[f52,f36])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f50])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f31,f59])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~spl3_1 | ~spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f32,f54,f50])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (5419)------------------------------
% 0.22/0.54  % (5419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5419)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (5419)Memory used [KB]: 6396
% 0.22/0.54  % (5419)Time elapsed: 0.125 s
% 0.22/0.54  % (5419)------------------------------
% 0.22/0.54  % (5419)------------------------------
% 0.22/0.54  % (5398)Refutation not found, incomplete strategy% (5398)------------------------------
% 0.22/0.54  % (5398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5398)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5398)Memory used [KB]: 1663
% 0.22/0.54  % (5398)Time elapsed: 0.123 s
% 0.22/0.54  % (5398)------------------------------
% 0.22/0.54  % (5398)------------------------------
% 0.22/0.54  % (5402)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (5423)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (5427)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (5394)Success in time 0.176 s
%------------------------------------------------------------------------------
