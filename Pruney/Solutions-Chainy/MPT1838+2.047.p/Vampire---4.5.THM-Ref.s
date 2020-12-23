%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 188 expanded)
%              Number of leaves         :   35 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  308 ( 595 expanded)
%              Number of equality atoms :   78 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f91,f111,f147,f163,f177,f191,f204,f214,f237,f298,f300,f301,f302,f345])).

fof(f345,plain,
    ( spl5_4
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl5_4
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f333,f73])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f333,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f99,f297,f257])).

fof(f257,plain,(
    ! [X0] :
      ( k1_tarski(sK4(X0)) = X0
      | v1_xboole_0(X0)
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f245,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ( k6_domain_1(X0,sK4(X0)) = X0
          & m1_subset_1(sK4(X0),X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK4(X0)) = X0
        & m1_subset_1(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X2] :
            ( k6_domain_1(X0,X2) = X0
            & m1_subset_1(X2,X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( k6_domain_1(X0,X1) = X0
          & m1_subset_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f245,plain,(
    ! [X0] :
      ( k1_tarski(sK4(X0)) = X0
      | ~ m1_subset_1(sK4(X0),X0)
      | v1_xboole_0(X0)
      | ~ sP0(X0) ) ),
    inference(superposition,[],[f49,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK4(X0)) = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f297,plain,
    ( ! [X3] : sK3 != k1_tarski(X3)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_31
  <=> ! [X3] : sK3 != k1_tarski(X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f99,plain,
    ( sP0(sK3)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_8
  <=> sP0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f302,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k4_xboole_0(sK2,sK3)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f301,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f300,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k4_xboole_0(sK2,sK3)
    | k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f298,plain,
    ( spl5_29
    | spl5_30
    | spl5_31
    | spl5_1
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f286,f160,f56,f296,f292,f288])).

fof(f288,plain,
    ( spl5_29
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f292,plain,
    ( spl5_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f56,plain,
    ( spl5_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f160,plain,
    ( spl5_16
  <=> sK3 = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f286,plain,
    ( ! [X3] :
        ( sK3 != k1_tarski(X3)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK3 )
    | spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f285,f58])).

fof(f58,plain,
    ( sK2 != sK3
    | spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f285,plain,
    ( ! [X3] :
        ( sK3 != k1_tarski(X3)
        | k1_xboole_0 = sK2
        | sK2 = sK3
        | k1_xboole_0 = sK3 )
    | ~ spl5_16 ),
    inference(superposition,[],[f53,f162])).

fof(f162,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f237,plain,
    ( ~ spl5_25
    | spl5_22 ),
    inference(avatar_split_clause,[],[f232,f211,f234])).

fof(f234,plain,
    ( spl5_25
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f211,plain,
    ( spl5_22
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f232,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK3)
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f213,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f213,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f214,plain,
    ( spl5_21
    | ~ spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f205,f201,f211,f207])).

fof(f207,plain,
    ( spl5_21
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f201,plain,
    ( spl5_20
  <=> r1_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f205,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl5_20 ),
    inference(resolution,[],[f203,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f203,plain,
    ( r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( spl5_20
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f198,f188,f201])).

fof(f188,plain,
    ( spl5_19
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f198,plain,
    ( r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl5_19 ),
    inference(superposition,[],[f46,f190])).

fof(f190,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f191,plain,
    ( spl5_19
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f178,f61,f188])).

fof(f61,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f178,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f177,plain,
    ( ~ spl5_18
    | spl5_13 ),
    inference(avatar_split_clause,[],[f166,f144,f174])).

fof(f174,plain,
    ( spl5_18
  <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f144,plain,
    ( spl5_13
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f166,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0)
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f146,f50])).

fof(f146,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f163,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f158,f61,f160])).

fof(f158,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f63,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f147,plain,
    ( ~ spl5_13
    | spl5_5 ),
    inference(avatar_split_clause,[],[f140,f76,f144])).

fof(f76,plain,
    ( spl5_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f140,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f78,f39,f47])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f78,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f111,plain,
    ( spl5_8
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f110,f88,f66,f97])).

fof(f66,plain,
    ( spl5_3
  <=> v1_zfmisc_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f88,plain,
    ( spl5_7
  <=> sP1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f110,plain,
    ( sP0(sK3)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f95,f68])).

fof(f68,plain,
    ( v1_zfmisc_1(sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f95,plain,
    ( ~ v1_zfmisc_1(sK3)
    | sP0(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f40,f90])).

fof(f90,plain,
    ( sP1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f40,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v1_zfmisc_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_zfmisc_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f91,plain,
    ( spl5_7
    | spl5_4 ),
    inference(avatar_split_clause,[],[f80,f71,f88])).

fof(f80,plain,
    ( sP1(sK3)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f14,f23,f22])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f79,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != sK3
    & r1_tarski(sK2,sK3)
    & v1_zfmisc_1(sK3)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK2 != X1
          & r1_tarski(sK2,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( sK2 != X1
        & r1_tarski(sK2,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK2 != sK3
      & r1_tarski(sK2,sK3)
      & v1_zfmisc_1(sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f74,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f56])).

fof(f38,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (17320)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (17313)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (17318)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (17320)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (17304)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (17310)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f346,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f91,f111,f147,f163,f177,f191,f204,f214,f237,f298,f300,f301,f302,f345])).
% 0.20/0.47  fof(f345,plain,(
% 0.20/0.47    spl5_4 | ~spl5_8 | ~spl5_31),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f344])).
% 0.20/0.47  fof(f344,plain,(
% 0.20/0.47    $false | (spl5_4 | ~spl5_8 | ~spl5_31)),
% 0.20/0.47    inference(subsumption_resolution,[],[f333,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~v1_xboole_0(sK3) | spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl5_4 <=> v1_xboole_0(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f333,plain,(
% 0.20/0.47    v1_xboole_0(sK3) | (~spl5_8 | ~spl5_31)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f99,f297,f257])).
% 0.20/0.47  fof(f257,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(sK4(X0)) = X0 | v1_xboole_0(X0) | ~sP0(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f245,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK4(X0),X0) | ~sP0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)) | ~sP0(X0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~sP0(X0)))),
% 0.20/0.47    inference(rectify,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~sP0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (sP0(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(sK4(X0)) = X0 | ~m1_subset_1(sK4(X0),X0) | v1_xboole_0(X0) | ~sP0(X0)) )),
% 0.20/0.47    inference(superposition,[],[f49,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0] : (k6_domain_1(X0,sK4(X0)) = X0 | ~sP0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.47  fof(f297,plain,(
% 0.20/0.47    ( ! [X3] : (sK3 != k1_tarski(X3)) ) | ~spl5_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f296])).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    spl5_31 <=> ! [X3] : sK3 != k1_tarski(X3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    sP0(sK3) | ~spl5_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl5_8 <=> sP0(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.47  fof(f302,plain,(
% 0.20/0.47    k1_xboole_0 != sK2 | k1_xboole_0 != k4_xboole_0(sK2,sK3) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f301,plain,(
% 0.20/0.47    k1_xboole_0 != sK2 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    k1_xboole_0 != sK3 | k1_xboole_0 != k4_xboole_0(sK2,sK3) | k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f298,plain,(
% 0.20/0.47    spl5_29 | spl5_30 | spl5_31 | spl5_1 | ~spl5_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f286,f160,f56,f296,f292,f288])).
% 0.20/0.47  fof(f288,plain,(
% 0.20/0.47    spl5_29 <=> k1_xboole_0 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    spl5_30 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl5_1 <=> sK2 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    spl5_16 <=> sK3 = k2_xboole_0(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.47  fof(f286,plain,(
% 0.20/0.47    ( ! [X3] : (sK3 != k1_tarski(X3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) ) | (spl5_1 | ~spl5_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f285,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    sK2 != sK3 | spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    ( ! [X3] : (sK3 != k1_tarski(X3) | k1_xboole_0 = sK2 | sK2 = sK3 | k1_xboole_0 = sK3) ) | ~spl5_16),
% 0.20/0.47    inference(superposition,[],[f53,f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    sK3 = k2_xboole_0(sK2,sK3) | ~spl5_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f160])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    ~spl5_25 | spl5_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f232,f211,f234])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    spl5_25 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    spl5_22 <=> r1_tarski(k1_xboole_0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.47  fof(f232,plain,(
% 0.20/0.47    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK3) | spl5_22),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f213,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,sK3) | spl5_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f211])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl5_21 | ~spl5_22 | ~spl5_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f205,f201,f211,f207])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    spl5_21 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    spl5_20 <=> r1_xboole_0(k1_xboole_0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,sK3) | v1_xboole_0(k1_xboole_0) | ~spl5_20),
% 0.20/0.47    inference(resolution,[],[f203,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    r1_xboole_0(k1_xboole_0,sK3) | ~spl5_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f201])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    spl5_20 | ~spl5_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f198,f188,f201])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    spl5_19 <=> k1_xboole_0 = k4_xboole_0(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    r1_xboole_0(k1_xboole_0,sK3) | ~spl5_19),
% 0.20/0.47    inference(superposition,[],[f46,f190])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK3) | ~spl5_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f188])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    spl5_19 | ~spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f178,f61,f188])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl5_2 <=> r1_tarski(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK3) | ~spl5_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f63,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f61])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ~spl5_18 | spl5_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f166,f144,f174])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl5_18 <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl5_13 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0) | spl5_13),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f146,f50])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k1_xboole_0) | spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f144])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl5_16 | ~spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f158,f61,f160])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    sK3 = k2_xboole_0(sK2,sK3) | ~spl5_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f63,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~spl5_13 | spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f140,f76,f144])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl5_5 <=> v1_xboole_0(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k1_xboole_0) | spl5_5),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f78,f39,f47])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ~v1_xboole_0(sK2) | spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl5_8 | ~spl5_3 | ~spl5_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f110,f88,f66,f97])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl5_3 <=> v1_zfmisc_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl5_7 <=> sP1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    sP0(sK3) | (~spl5_3 | ~spl5_7)),
% 0.20/0.47    inference(subsumption_resolution,[],[f95,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    v1_zfmisc_1(sK3) | ~spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ~v1_zfmisc_1(sK3) | sP0(sK3) | ~spl5_7),
% 0.20/0.47    inference(resolution,[],[f40,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    sP1(sK3) | ~spl5_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (~sP1(X0) | ~v1_zfmisc_1(X0) | sP0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_zfmisc_1(X0))) | ~sP1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : ((v1_zfmisc_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl5_7 | spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f80,f71,f88])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    sP1(sK3) | spl5_4),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f73,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (sP1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (sP1(X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(definition_folding,[],[f14,f23,f22])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f76])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~v1_xboole_0(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    (sK2 != sK3 & r1_tarski(sK2,sK3) & v1_zfmisc_1(sK3) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f26,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK2 != X1 & r1_tarski(sK2,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X1] : (sK2 != X1 & r1_tarski(sK2,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK2 != sK3 & r1_tarski(sK2,sK3) & v1_zfmisc_1(sK3) & ~v1_xboole_0(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ~spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f71])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~v1_xboole_0(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f66])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v1_zfmisc_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f61])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f56])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    sK2 != sK3),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (17320)------------------------------
% 0.20/0.47  % (17320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17320)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (17320)Memory used [KB]: 10746
% 0.20/0.47  % (17320)Time elapsed: 0.063 s
% 0.20/0.47  % (17320)------------------------------
% 0.20/0.47  % (17320)------------------------------
% 0.20/0.47  % (17311)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (17303)Success in time 0.12 s
%------------------------------------------------------------------------------
