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
% DateTime   : Thu Dec  3 13:05:23 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 297 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  572 (1202 expanded)
%              Number of equality atoms :   83 ( 169 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f97,f103,f114,f119,f128,f140,f155,f169,f319,f329,f343,f358,f372,f373])).

fof(f373,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 != k6_relat_1(k1_relat_1(sK2))
    | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f372,plain,
    ( ~ spl3_9
    | ~ spl3_11
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_11
    | spl3_31 ),
    inference(subsumption_resolution,[],[f370,f113])).

fof(f113,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f370,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_11
    | spl3_31 ),
    inference(subsumption_resolution,[],[f368,f127])).

fof(f127,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_11
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f368,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_31 ),
    inference(resolution,[],[f357,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f357,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl3_31
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f358,plain,
    ( ~ spl3_31
    | spl3_29
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f353,f326,f316,f355])).

fof(f316,plain,
    ( spl3_29
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f326,plain,
    ( spl3_30
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f353,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_29
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f352,f318])).

fof(f318,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f316])).

fof(f352,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_30 ),
    inference(resolution,[],[f328,f196])).

fof(f196,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f104,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f104,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f328,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f326])).

fof(f343,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_16
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_16
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f96,f86,f81,f91,f168,f270,f232])).

fof(f232,plain,
    ( ! [X43,X41,X42,X40] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X42,X40),sK1)
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(sK0,X43)))
        | ~ v1_funct_1(X42)
        | sK1 = k5_relat_1(X42,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X41,sK0))) )
    | ~ spl3_6 ),
    inference(resolution,[],[f175,f157])).

fof(f157,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK1 = X1
        | ~ r2_relset_1(sK0,sK0,X1,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f91])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f175,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f56,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f270,plain,
    ( sK1 != k5_relat_1(sK1,sK2)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_25
  <=> sK1 = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f168,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_16
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f96,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_7
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f329,plain,
    ( spl3_30
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f324,f269,f150,f116,f111,f94,f84,f326])).

fof(f116,plain,
    ( spl3_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f150,plain,
    ( spl3_15
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f324,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f323,f152])).

fof(f152,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f323,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f322,f113])).

% (8105)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f322,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f321,f86])).

fof(f321,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f320,f118])).

fof(f118,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f320,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f302,f96])).

fof(f302,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f301])).

fof(f301,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_25 ),
    inference(superposition,[],[f54,f271])).

fof(f271,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f319,plain,
    ( spl3_28
    | ~ spl3_29
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f310,f269,f150,f116,f111,f94,f84,f316,f312])).

fof(f312,plain,
    ( spl3_28
  <=> sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

% (8104)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f310,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f309,f152])).

fof(f309,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f308,f118])).

fof(f308,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f307,f96])).

fof(f307,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f306,f113])).

fof(f306,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f303,f86])).

fof(f303,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f300])).

fof(f300,plain,
    ( sK1 != sK1
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_25 ),
    inference(superposition,[],[f53,f271])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k1_relat_1(X1) = k2_relat_1(X0) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f169,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f164,f94,f89,f84,f79,f74,f166])).

fof(f74,plain,
    ( spl3_3
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f164,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f163,f96])).

fof(f163,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f162,f91])).

fof(f162,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f161,f86])).

fof(f161,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f158,f81])).

fof(f158,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f76,f47])).

fof(f76,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f155,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f154,f89,f69,f150])).

fof(f69,plain,
    ( spl3_2
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f154,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f147,f91])).

fof(f147,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f71,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f71,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f140,plain,
    ( spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f134,f79,f137])).

fof(f137,plain,
    ( spl3_13
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f134,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f62,f81])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f122,f79,f125])).

fof(f122,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f60,f81])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f109,f89,f116])).

% (8103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f109,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f57,f91])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f108,f79,f111])).

fof(f108,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f57,f81])).

fof(f103,plain,
    ( ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f98,f64,f100])).

fof(f100,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f64,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f98,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))
    | spl3_1 ),
    inference(backward_demodulation,[],[f66,f46])).

fof(f46,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f12])).

% (8098)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f12,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f97,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f39,f94])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

% (8080)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f36,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & k2_relset_1(X0,X0,X1) = X0
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & sK0 = k2_relset_1(sK0,sK0,sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & sK0 = k2_relset_1(sK0,sK0,sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & sK0 = k2_relset_1(sK0,sK0,sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).

fof(f92,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f79])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f69])).

fof(f44,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f64])).

fof(f45,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:31:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.35/0.55  % (8101)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.55  % (8079)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.55  % (8093)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.56  % (8099)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.57  % (8087)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.57  % (8085)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.57  % (8081)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.57/0.57  % (8083)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.57  % (8082)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.58  % (8091)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.58  % (8084)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.59  % (8078)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.59  % (8099)Refutation found. Thanks to Tanya!
% 1.57/0.59  % SZS status Theorem for theBenchmark
% 1.57/0.60  % (8092)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.57/0.60  % SZS output start Proof for theBenchmark
% 1.57/0.60  fof(f374,plain,(
% 1.57/0.60    $false),
% 1.57/0.60    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f97,f103,f114,f119,f128,f140,f155,f169,f319,f329,f343,f358,f372,f373])).
% 1.57/0.60  fof(f373,plain,(
% 1.57/0.60    sK0 != k1_relat_1(sK2) | sK2 != k6_relat_1(k1_relat_1(sK2)) | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f372,plain,(
% 1.57/0.60    ~spl3_9 | ~spl3_11 | spl3_31),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f371])).
% 1.57/0.60  fof(f371,plain,(
% 1.57/0.60    $false | (~spl3_9 | ~spl3_11 | spl3_31)),
% 1.57/0.60    inference(subsumption_resolution,[],[f370,f113])).
% 1.57/0.60  fof(f113,plain,(
% 1.57/0.60    v1_relat_1(sK2) | ~spl3_9),
% 1.57/0.60    inference(avatar_component_clause,[],[f111])).
% 1.57/0.60  fof(f111,plain,(
% 1.57/0.60    spl3_9 <=> v1_relat_1(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.57/0.60  fof(f370,plain,(
% 1.57/0.60    ~v1_relat_1(sK2) | (~spl3_11 | spl3_31)),
% 1.57/0.60    inference(subsumption_resolution,[],[f368,f127])).
% 1.57/0.60  fof(f127,plain,(
% 1.57/0.60    v4_relat_1(sK2,sK0) | ~spl3_11),
% 1.57/0.60    inference(avatar_component_clause,[],[f125])).
% 1.57/0.60  fof(f125,plain,(
% 1.57/0.60    spl3_11 <=> v4_relat_1(sK2,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.57/0.60  fof(f368,plain,(
% 1.57/0.60    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_31),
% 1.57/0.60    inference(resolution,[],[f357,f58])).
% 1.57/0.60  fof(f58,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f38])).
% 1.57/0.60  fof(f38,plain,(
% 1.57/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(nnf_transformation,[],[f32])).
% 1.57/0.60  fof(f32,plain,(
% 1.57/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f3])).
% 1.57/0.60  fof(f3,axiom,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.57/0.60  fof(f357,plain,(
% 1.57/0.60    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_31),
% 1.57/0.60    inference(avatar_component_clause,[],[f355])).
% 1.57/0.60  fof(f355,plain,(
% 1.57/0.60    spl3_31 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.57/0.60  fof(f358,plain,(
% 1.57/0.60    ~spl3_31 | spl3_29 | ~spl3_30),
% 1.57/0.60    inference(avatar_split_clause,[],[f353,f326,f316,f355])).
% 1.57/0.60  fof(f316,plain,(
% 1.57/0.60    spl3_29 <=> sK0 = k1_relat_1(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.57/0.60  fof(f326,plain,(
% 1.57/0.60    spl3_30 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.57/0.60  fof(f353,plain,(
% 1.57/0.60    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl3_29 | ~spl3_30)),
% 1.57/0.60    inference(subsumption_resolution,[],[f352,f318])).
% 1.57/0.60  fof(f318,plain,(
% 1.57/0.60    sK0 != k1_relat_1(sK2) | spl3_29),
% 1.57/0.60    inference(avatar_component_clause,[],[f316])).
% 1.57/0.60  fof(f352,plain,(
% 1.57/0.60    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_30),
% 1.57/0.60    inference(resolution,[],[f328,f196])).
% 1.57/0.60  fof(f196,plain,(
% 1.57/0.60    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 1.57/0.60    inference(superposition,[],[f104,f51])).
% 1.57/0.60  fof(f51,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f24,plain,(
% 1.57/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f2])).
% 1.57/0.60  fof(f2,axiom,(
% 1.57/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.57/0.60  fof(f104,plain,(
% 1.57/0.60    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 1.57/0.60    inference(superposition,[],[f51,f52])).
% 1.57/0.60  fof(f52,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f1])).
% 1.57/0.60  fof(f1,axiom,(
% 1.57/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.57/0.60  fof(f328,plain,(
% 1.57/0.60    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl3_30),
% 1.57/0.60    inference(avatar_component_clause,[],[f326])).
% 1.57/0.60  fof(f343,plain,(
% 1.57/0.60    ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_16 | spl3_25),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f342])).
% 1.57/0.60  fof(f342,plain,(
% 1.57/0.60    $false | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_16 | spl3_25)),
% 1.57/0.60    inference(unit_resulting_resolution,[],[f96,f86,f81,f91,f168,f270,f232])).
% 1.57/0.60  fof(f232,plain,(
% 1.57/0.60    ( ! [X43,X41,X42,X40] : (~r2_relset_1(sK0,sK0,k5_relat_1(X42,X40),sK1) | ~v1_funct_1(X40) | ~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(sK0,X43))) | ~v1_funct_1(X42) | sK1 = k5_relat_1(X42,X40) | ~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X41,sK0)))) ) | ~spl3_6),
% 1.57/0.60    inference(resolution,[],[f175,f157])).
% 1.57/0.60  fof(f157,plain,(
% 1.57/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X1 | ~r2_relset_1(sK0,sK0,X1,sK1)) ) | ~spl3_6),
% 1.57/0.60    inference(resolution,[],[f48,f91])).
% 1.57/0.60  fof(f48,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f37])).
% 1.57/0.60  fof(f37,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(nnf_transformation,[],[f22])).
% 1.57/0.60  fof(f22,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(flattening,[],[f21])).
% 1.57/0.60  fof(f21,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.60    inference(ennf_transformation,[],[f9])).
% 1.57/0.60  fof(f9,axiom,(
% 1.57/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.57/0.60  fof(f175,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f174])).
% 1.57/0.60  fof(f174,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.60    inference(superposition,[],[f56,f47])).
% 1.57/0.60  fof(f47,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f20])).
% 1.57/0.60  fof(f20,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.60    inference(flattening,[],[f19])).
% 1.57/0.60  fof(f19,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.60    inference(ennf_transformation,[],[f11])).
% 1.57/0.60  fof(f11,axiom,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.57/0.60  fof(f56,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f30])).
% 1.57/0.60  fof(f30,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.60    inference(flattening,[],[f29])).
% 1.57/0.60  fof(f29,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.60    inference(ennf_transformation,[],[f10])).
% 1.57/0.60  fof(f10,axiom,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.57/0.60  fof(f270,plain,(
% 1.57/0.60    sK1 != k5_relat_1(sK1,sK2) | spl3_25),
% 1.57/0.60    inference(avatar_component_clause,[],[f269])).
% 1.57/0.60  fof(f269,plain,(
% 1.57/0.60    spl3_25 <=> sK1 = k5_relat_1(sK1,sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.57/0.60  fof(f168,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | ~spl3_16),
% 1.57/0.60    inference(avatar_component_clause,[],[f166])).
% 1.57/0.60  fof(f166,plain,(
% 1.57/0.60    spl3_16 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.57/0.60  fof(f91,plain,(
% 1.57/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_6),
% 1.57/0.60    inference(avatar_component_clause,[],[f89])).
% 1.57/0.60  fof(f89,plain,(
% 1.57/0.60    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.57/0.60  fof(f81,plain,(
% 1.57/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 1.57/0.60    inference(avatar_component_clause,[],[f79])).
% 1.57/0.60  fof(f79,plain,(
% 1.57/0.60    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.57/0.60  fof(f86,plain,(
% 1.57/0.60    v1_funct_1(sK2) | ~spl3_5),
% 1.57/0.60    inference(avatar_component_clause,[],[f84])).
% 1.57/0.60  fof(f84,plain,(
% 1.57/0.60    spl3_5 <=> v1_funct_1(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.57/0.60  fof(f96,plain,(
% 1.57/0.60    v1_funct_1(sK1) | ~spl3_7),
% 1.57/0.60    inference(avatar_component_clause,[],[f94])).
% 1.57/0.60  fof(f94,plain,(
% 1.57/0.60    spl3_7 <=> v1_funct_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.57/0.60  fof(f329,plain,(
% 1.57/0.60    spl3_30 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_15 | ~spl3_25),
% 1.57/0.60    inference(avatar_split_clause,[],[f324,f269,f150,f116,f111,f94,f84,f326])).
% 1.57/0.60  fof(f116,plain,(
% 1.57/0.60    spl3_10 <=> v1_relat_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.57/0.60  fof(f150,plain,(
% 1.57/0.60    spl3_15 <=> sK0 = k2_relat_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.57/0.60  fof(f324,plain,(
% 1.57/0.60    r1_tarski(sK0,k1_relat_1(sK2)) | (~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_15 | ~spl3_25)),
% 1.57/0.60    inference(forward_demodulation,[],[f323,f152])).
% 1.57/0.60  fof(f152,plain,(
% 1.57/0.60    sK0 = k2_relat_1(sK1) | ~spl3_15),
% 1.57/0.60    inference(avatar_component_clause,[],[f150])).
% 1.57/0.60  fof(f323,plain,(
% 1.57/0.60    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | (~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f322,f113])).
% 1.57/0.60  % (8105)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.60  fof(f322,plain,(
% 1.57/0.60    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_5 | ~spl3_7 | ~spl3_10 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f321,f86])).
% 1.57/0.60  fof(f321,plain,(
% 1.57/0.60    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_7 | ~spl3_10 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f320,f118])).
% 1.57/0.60  fof(f118,plain,(
% 1.57/0.60    v1_relat_1(sK1) | ~spl3_10),
% 1.57/0.60    inference(avatar_component_clause,[],[f116])).
% 1.57/0.60  fof(f320,plain,(
% 1.57/0.60    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_7 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f302,f96])).
% 1.57/0.60  fof(f302,plain,(
% 1.57/0.60    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_25),
% 1.57/0.60    inference(trivial_inequality_removal,[],[f301])).
% 1.57/0.60  fof(f301,plain,(
% 1.57/0.60    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_25),
% 1.57/0.60    inference(superposition,[],[f54,f271])).
% 1.57/0.60  fof(f271,plain,(
% 1.57/0.60    sK1 = k5_relat_1(sK1,sK2) | ~spl3_25),
% 1.57/0.60    inference(avatar_component_clause,[],[f269])).
% 1.57/0.60  fof(f54,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f28])).
% 1.57/0.60  fof(f28,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(flattening,[],[f27])).
% 1.57/0.60  fof(f27,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 1.57/0.60  fof(f319,plain,(
% 1.57/0.60    spl3_28 | ~spl3_29 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_15 | ~spl3_25),
% 1.57/0.60    inference(avatar_split_clause,[],[f310,f269,f150,f116,f111,f94,f84,f316,f312])).
% 1.57/0.60  fof(f312,plain,(
% 1.57/0.60    spl3_28 <=> sK2 = k6_relat_1(k1_relat_1(sK2))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.57/0.60  % (8104)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.60  fof(f310,plain,(
% 1.57/0.60    sK0 != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | (~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_15 | ~spl3_25)),
% 1.57/0.60    inference(forward_demodulation,[],[f309,f152])).
% 1.57/0.60  fof(f309,plain,(
% 1.57/0.60    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK1) | (~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f308,f118])).
% 1.57/0.60  fof(f308,plain,(
% 1.57/0.60    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | (~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f307,f96])).
% 1.57/0.60  fof(f307,plain,(
% 1.57/0.60    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_5 | ~spl3_9 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f306,f113])).
% 1.57/0.60  fof(f306,plain,(
% 1.57/0.60    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_5 | ~spl3_25)),
% 1.57/0.60    inference(subsumption_resolution,[],[f303,f86])).
% 1.57/0.60  fof(f303,plain,(
% 1.57/0.60    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_25),
% 1.57/0.60    inference(trivial_inequality_removal,[],[f300])).
% 1.57/0.60  fof(f300,plain,(
% 1.57/0.60    sK1 != sK1 | sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_25),
% 1.57/0.60    inference(superposition,[],[f53,f271])).
% 1.57/0.60  fof(f53,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f26])).
% 1.57/0.60  fof(f26,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(flattening,[],[f25])).
% 1.57/0.60  fof(f25,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f5])).
% 1.57/0.60  fof(f5,axiom,(
% 1.57/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 1.57/0.60  fof(f169,plain,(
% 1.57/0.60    spl3_16 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7),
% 1.57/0.60    inference(avatar_split_clause,[],[f164,f94,f89,f84,f79,f74,f166])).
% 1.57/0.60  fof(f74,plain,(
% 1.57/0.60    spl3_3 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.57/0.60  fof(f164,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7)),
% 1.57/0.60    inference(subsumption_resolution,[],[f163,f96])).
% 1.57/0.60  fof(f163,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 1.57/0.60    inference(subsumption_resolution,[],[f162,f91])).
% 1.57/0.60  fof(f162,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 1.57/0.60    inference(subsumption_resolution,[],[f161,f86])).
% 1.57/0.60  fof(f161,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4)),
% 1.57/0.60    inference(subsumption_resolution,[],[f158,f81])).
% 1.57/0.60  fof(f158,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_3),
% 1.57/0.60    inference(superposition,[],[f76,f47])).
% 1.57/0.60  fof(f76,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) | ~spl3_3),
% 1.57/0.60    inference(avatar_component_clause,[],[f74])).
% 1.57/0.60  fof(f155,plain,(
% 1.57/0.60    spl3_15 | ~spl3_2 | ~spl3_6),
% 1.57/0.60    inference(avatar_split_clause,[],[f154,f89,f69,f150])).
% 1.57/0.60  fof(f69,plain,(
% 1.57/0.60    spl3_2 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.57/0.60  fof(f154,plain,(
% 1.57/0.60    sK0 = k2_relat_1(sK1) | (~spl3_2 | ~spl3_6)),
% 1.57/0.60    inference(subsumption_resolution,[],[f147,f91])).
% 1.57/0.60  fof(f147,plain,(
% 1.57/0.60    sK0 = k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_2),
% 1.57/0.60    inference(superposition,[],[f71,f50])).
% 1.57/0.60  fof(f50,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f23])).
% 1.57/0.60  fof(f23,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.57/0.60  fof(f71,plain,(
% 1.57/0.60    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl3_2),
% 1.57/0.60    inference(avatar_component_clause,[],[f69])).
% 1.57/0.60  fof(f140,plain,(
% 1.57/0.60    spl3_13 | ~spl3_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f134,f79,f137])).
% 1.57/0.60  fof(f137,plain,(
% 1.57/0.60    spl3_13 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.57/0.60  fof(f134,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_4),
% 1.57/0.60    inference(resolution,[],[f62,f81])).
% 1.57/0.60  fof(f62,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f61])).
% 1.57/0.60  fof(f61,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(equality_resolution,[],[f49])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f37])).
% 1.57/0.60  fof(f128,plain,(
% 1.57/0.60    spl3_11 | ~spl3_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f122,f79,f125])).
% 1.57/0.60  fof(f122,plain,(
% 1.57/0.60    v4_relat_1(sK2,sK0) | ~spl3_4),
% 1.57/0.60    inference(resolution,[],[f60,f81])).
% 1.57/0.60  fof(f60,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f33])).
% 1.57/0.60  fof(f33,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f16])).
% 1.57/0.60  fof(f16,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f7])).
% 1.57/0.60  fof(f7,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.60  fof(f119,plain,(
% 1.57/0.60    spl3_10 | ~spl3_6),
% 1.57/0.60    inference(avatar_split_clause,[],[f109,f89,f116])).
% 1.57/0.60  % (8103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.60  fof(f109,plain,(
% 1.57/0.60    v1_relat_1(sK1) | ~spl3_6),
% 1.57/0.60    inference(resolution,[],[f57,f91])).
% 1.57/0.60  fof(f57,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f31])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f6])).
% 1.57/0.60  fof(f6,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.57/0.60  fof(f114,plain,(
% 1.57/0.60    spl3_9 | ~spl3_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f108,f79,f111])).
% 1.57/0.60  fof(f108,plain,(
% 1.57/0.60    v1_relat_1(sK2) | ~spl3_4),
% 1.57/0.60    inference(resolution,[],[f57,f81])).
% 1.57/0.60  fof(f103,plain,(
% 1.57/0.60    ~spl3_8 | spl3_1),
% 1.57/0.60    inference(avatar_split_clause,[],[f98,f64,f100])).
% 1.57/0.60  fof(f100,plain,(
% 1.57/0.60    spl3_8 <=> r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.57/0.60  fof(f64,plain,(
% 1.57/0.60    spl3_1 <=> r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.57/0.60  fof(f98,plain,(
% 1.57/0.60    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) | spl3_1),
% 1.57/0.60    inference(backward_demodulation,[],[f66,f46])).
% 1.57/0.60  fof(f46,plain,(
% 1.57/0.60    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f12])).
% 1.57/0.60  % (8098)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.57/0.60  fof(f12,axiom,(
% 1.57/0.60    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.57/0.60  fof(f66,plain,(
% 1.57/0.60    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) | spl3_1),
% 1.57/0.60    inference(avatar_component_clause,[],[f64])).
% 1.57/0.60  fof(f97,plain,(
% 1.57/0.60    spl3_7),
% 1.57/0.60    inference(avatar_split_clause,[],[f39,f94])).
% 1.57/0.60  fof(f39,plain,(
% 1.57/0.60    v1_funct_1(sK1)),
% 1.57/0.60    inference(cnf_transformation,[],[f36])).
% 1.57/0.60  % (8080)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.60  fof(f36,plain,(
% 1.57/0.60    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34])).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f35,plain,(
% 1.57/0.60    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f18,plain,(
% 1.57/0.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.57/0.60    inference(flattening,[],[f17])).
% 1.57/0.60  fof(f17,plain,(
% 1.57/0.60    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f15])).
% 1.57/0.60  fof(f15,plain,(
% 1.57/0.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f14])).
% 1.57/0.60  fof(f14,negated_conjecture,(
% 1.57/0.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.57/0.60    inference(negated_conjecture,[],[f13])).
% 1.57/0.61  fof(f13,conjecture,(
% 1.57/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).
% 1.57/0.61  fof(f92,plain,(
% 1.57/0.61    spl3_6),
% 1.57/0.61    inference(avatar_split_clause,[],[f40,f89])).
% 1.57/0.61  fof(f40,plain,(
% 1.57/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  fof(f87,plain,(
% 1.57/0.61    spl3_5),
% 1.57/0.61    inference(avatar_split_clause,[],[f41,f84])).
% 1.57/0.61  fof(f41,plain,(
% 1.57/0.61    v1_funct_1(sK2)),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  fof(f82,plain,(
% 1.57/0.61    spl3_4),
% 1.57/0.61    inference(avatar_split_clause,[],[f42,f79])).
% 1.57/0.61  fof(f42,plain,(
% 1.57/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  fof(f77,plain,(
% 1.57/0.61    spl3_3),
% 1.57/0.61    inference(avatar_split_clause,[],[f43,f74])).
% 1.57/0.61  fof(f43,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  fof(f72,plain,(
% 1.57/0.61    spl3_2),
% 1.57/0.61    inference(avatar_split_clause,[],[f44,f69])).
% 1.57/0.61  fof(f44,plain,(
% 1.57/0.61    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  fof(f67,plain,(
% 1.57/0.61    ~spl3_1),
% 1.57/0.61    inference(avatar_split_clause,[],[f45,f64])).
% 1.57/0.61  fof(f45,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  % SZS output end Proof for theBenchmark
% 1.57/0.61  % (8099)------------------------------
% 1.57/0.61  % (8099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (8099)Termination reason: Refutation
% 1.57/0.61  
% 1.57/0.61  % (8099)Memory used [KB]: 6524
% 1.57/0.61  % (8099)Time elapsed: 0.171 s
% 1.57/0.61  % (8099)------------------------------
% 1.57/0.61  % (8099)------------------------------
% 1.57/0.61  % (8077)Success in time 0.242 s
%------------------------------------------------------------------------------
