%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 184 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 ( 628 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f116,f126,f303,f357,f365,f521,f585])).

fof(f585,plain,
    ( spl6_14
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl6_14
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f581,f518])).

fof(f518,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f516])).

fof(f516,plain,
    ( spl6_22
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f581,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl6_14 ),
    inference(superposition,[],[f444,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f81,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f81,plain,(
    ! [X0] : v1_xboole_0(k4_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f40,f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f444,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k4_xboole_0(sK3,X0))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f304,f54,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f54,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f19,f18])).

fof(f18,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f304,plain,
    ( ! [X0] : ~ sP0(X0,sK2,sK3)
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f300,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f300,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl6_14
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f521,plain,
    ( spl6_22
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f520,f362,f123,f516])).

fof(f123,plain,
    ( spl6_8
  <=> k1_xboole_0 = k4_xboole_0(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f362,plain,
    ( spl6_16
  <=> sP0(sK3,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f520,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f502,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k4_xboole_0(sK4,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f502,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK4,sK3))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f364,f54,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f364,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f362])).

fof(f365,plain,
    ( spl6_16
    | spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f359,f352,f298,f362])).

fof(f352,plain,
    ( spl6_15
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f359,plain,
    ( sP0(sK3,sK2,sK4)
    | spl6_14
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f300,f354,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f354,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f352])).

fof(f357,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f356,f71,f56,f352])).

fof(f56,plain,
    ( spl6_1
  <=> v3_setfam_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f71,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f356,plain,
    ( r2_hidden(sK2,sK4)
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f349,f58])).

fof(f58,plain,
    ( ~ v3_setfam_1(sK4,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f349,plain,
    ( r2_hidden(sK2,sK4)
    | v3_setfam_1(sK4,sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f43,f73])).

fof(f73,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f303,plain,
    ( ~ spl6_14
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f302,f76,f66,f298])).

fof(f66,plain,
    ( spl6_3
  <=> v3_setfam_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f76,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f302,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f296,f68])).

fof(f68,plain,
    ( v3_setfam_1(sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f296,plain,
    ( ~ v3_setfam_1(sK3,sK2)
    | ~ r2_hidden(sK2,sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f42,f78])).

fof(f78,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_setfam_1(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f126,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f121,f113,f123])).

fof(f113,plain,
    ( spl6_7
  <=> v1_xboole_0(k4_xboole_0(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f121,plain,
    ( k1_xboole_0 = k4_xboole_0(sK4,sK3)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f115,f38])).

fof(f115,plain,
    ( v1_xboole_0(k4_xboole_0(sK4,sK3))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( spl6_7
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f110,f61,f113])).

fof(f61,plain,
    ( spl6_2
  <=> r1_tarski(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f110,plain,
    ( v1_xboole_0(k4_xboole_0(sK4,sK3))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f39,f102,f41])).

fof(f102,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK4,X0),sK3)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f40,f63,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f63,plain,
    ( r1_tarski(sK4,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f79,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v3_setfam_1(sK4,sK2)
    & r1_tarski(sK4,sK3)
    & v3_setfam_1(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(X2,X0)
            & r1_tarski(X2,X1)
            & v3_setfam_1(X1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(X2,sK2)
          & r1_tarski(X2,sK3)
          & v3_setfam_1(sK3,sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(X2,sK2)
        & r1_tarski(X2,sK3)
        & v3_setfam_1(sK3,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
   => ( ~ v3_setfam_1(sK4,sK2)
      & r1_tarski(sK4,sK3)
      & v3_setfam_1(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

fof(f74,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    v3_setfam_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    ~ v3_setfam_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (19717)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (19724)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (19713)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (19710)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (19720)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (19724)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (19726)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (19712)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f586,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f116,f126,f303,f357,f365,f521,f585])).
% 0.20/0.49  fof(f585,plain,(
% 0.20/0.49    spl6_14 | ~spl6_22),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f584])).
% 0.20/0.49  fof(f584,plain,(
% 0.20/0.49    $false | (spl6_14 | ~spl6_22)),
% 0.20/0.49    inference(subsumption_resolution,[],[f581,f518])).
% 0.20/0.49  fof(f518,plain,(
% 0.20/0.49    r2_hidden(sK2,k1_xboole_0) | ~spl6_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f516])).
% 0.20/0.49  fof(f516,plain,(
% 0.20/0.49    spl6_22 <=> r2_hidden(sK2,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.49  fof(f581,plain,(
% 0.20/0.49    ~r2_hidden(sK2,k1_xboole_0) | spl6_14),
% 0.20/0.49    inference(superposition,[],[f444,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f81,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(k4_xboole_0(X0,X0))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f39,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f444,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2,k4_xboole_0(sK3,X0))) ) | spl6_14),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f304,f54,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.49    inference(rectify,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.20/0.49    inference(definition_folding,[],[f1,f19,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ( ! [X0] : (~sP0(X0,sK2,sK3)) ) | spl6_14),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f300,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.49    inference(rectify,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    ~r2_hidden(sK2,sK3) | spl6_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f298])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    spl6_14 <=> r2_hidden(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.49  fof(f521,plain,(
% 0.20/0.49    spl6_22 | ~spl6_8 | ~spl6_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f520,f362,f123,f516])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl6_8 <=> k1_xboole_0 = k4_xboole_0(sK4,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.49  fof(f362,plain,(
% 0.20/0.49    spl6_16 <=> sP0(sK3,sK2,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.49  fof(f520,plain,(
% 0.20/0.49    r2_hidden(sK2,k1_xboole_0) | (~spl6_8 | ~spl6_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f502,f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK4,sK3) | ~spl6_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f123])).
% 0.20/0.49  fof(f502,plain,(
% 0.20/0.49    r2_hidden(sK2,k4_xboole_0(sK4,sK3)) | ~spl6_16),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f364,f54,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f364,plain,(
% 0.20/0.49    sP0(sK3,sK2,sK4) | ~spl6_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f362])).
% 0.20/0.49  fof(f365,plain,(
% 0.20/0.49    spl6_16 | spl6_14 | ~spl6_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f359,f352,f298,f362])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    spl6_15 <=> r2_hidden(sK2,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    sP0(sK3,sK2,sK4) | (spl6_14 | ~spl6_15)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f300,f354,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    r2_hidden(sK2,sK4) | ~spl6_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f352])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    spl6_15 | spl6_1 | ~spl6_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f356,f71,f56,f352])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl6_1 <=> v3_setfam_1(sK4,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    r2_hidden(sK2,sK4) | (spl6_1 | ~spl6_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f349,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~v3_setfam_1(sK4,sK2) | spl6_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    r2_hidden(sK2,sK4) | v3_setfam_1(sK4,sK2) | ~spl6_4),
% 0.20/0.49    inference(resolution,[],[f43,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~spl6_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    ~spl6_14 | ~spl6_3 | ~spl6_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f302,f76,f66,f298])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl6_3 <=> v3_setfam_1(sK3,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    ~r2_hidden(sK2,sK3) | (~spl6_3 | ~spl6_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f296,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v3_setfam_1(sK3,sK2) | ~spl6_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    ~v3_setfam_1(sK3,sK2) | ~r2_hidden(sK2,sK3) | ~spl6_5),
% 0.20/0.49    inference(resolution,[],[f42,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~spl6_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_setfam_1(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl6_8 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f121,f113,f123])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl6_7 <=> v1_xboole_0(k4_xboole_0(sK4,sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK4,sK3) | ~spl6_7),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f115,f38])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    v1_xboole_0(k4_xboole_0(sK4,sK3)) | ~spl6_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl6_7 | ~spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f110,f61,f113])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl6_2 <=> r1_tarski(sK4,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    v1_xboole_0(k4_xboole_0(sK4,sK3)) | ~spl6_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f39,f102,f41])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k4_xboole_0(sK4,X0),sK3)) ) | ~spl6_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f63,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r1_tarski(sK4,sK3) | ~spl6_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl6_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f76])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    (~v3_setfam_1(sK4,sK2) & r1_tarski(sK4,sK3) & v3_setfam_1(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f22,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~v3_setfam_1(X2,sK2) & r1_tarski(X2,sK3) & v3_setfam_1(sK3,sK2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X2] : (~v3_setfam_1(X2,sK2) & r1_tarski(X2,sK3) & v3_setfam_1(sK3,sK2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) => (~v3_setfam_1(sK4,sK2) & r1_tarski(sK4,sK3) & v3_setfam_1(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : ((~v3_setfam_1(X2,X0) & (r1_tarski(X2,X1) & v3_setfam_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl6_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f71])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl6_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f66])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v3_setfam_1(sK3,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f61])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    r1_tarski(sK4,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ~spl6_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f56])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~v3_setfam_1(sK4,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (19724)------------------------------
% 0.20/0.49  % (19724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19724)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (19724)Memory used [KB]: 10874
% 0.20/0.49  % (19724)Time elapsed: 0.079 s
% 0.20/0.49  % (19724)------------------------------
% 0.20/0.49  % (19724)------------------------------
% 0.20/0.49  % (19707)Success in time 0.138 s
%------------------------------------------------------------------------------
