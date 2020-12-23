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
% DateTime   : Thu Dec  3 13:22:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 346 expanded)
%              Number of leaves         :   27 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  513 (2299 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f126,f131,f156,f183,f215,f218,f236,f277,f279,f284])).

fof(f284,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl8_10 ),
    inference(subsumption_resolution,[],[f282,f49])).

fof(f49,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    & v3_tex_2(sK5,sK4)
    & ( v4_pre_topc(sK5,sK4)
      | v3_pre_topc(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v3_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK4))
          & v3_tex_2(X1,sK4)
          & ( v4_pre_topc(X1,sK4)
            | v3_pre_topc(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v3_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK4))
        & v3_tex_2(X1,sK4)
        & ( v4_pre_topc(X1,sK4)
          | v3_pre_topc(X1,sK4) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( v1_subset_1(sK5,u1_struct_0(sK4))
      & v3_tex_2(sK5,sK4)
      & ( v4_pre_topc(sK5,sK4)
        | v3_pre_topc(sK5,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(f282,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_10 ),
    inference(subsumption_resolution,[],[f281,f48])).

fof(f48,plain,(
    v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f281,plain,
    ( ~ v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | spl8_10 ),
    inference(subsumption_resolution,[],[f280,f47])).

fof(f47,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f280,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | spl8_10 ),
    inference(resolution,[],[f245,f91])).

fof(f91,plain,(
    ! [X1] :
      ( sP0(X1)
      | ~ v2_pre_topc(X1)
      | ~ v3_tdlat_3(X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f67,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v3_tdlat_3(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v3_tdlat_3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f67,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f25,f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f245,plain,
    ( ~ sP0(sK4)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_10
  <=> sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f279,plain,
    ( ~ spl8_10
    | spl8_2
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f278,f81,f85,f243])).

fof(f85,plain,
    ( spl8_2
  <=> v4_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f81,plain,
    ( spl8_1
  <=> v3_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f278,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ sP0(sK4)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f115,f83])).

fof(f83,plain,
    ( v3_pre_topc(sK5,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f115,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ sP0(sK4) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | v4_pre_topc(X2,X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ v4_pre_topc(sK6(X0),X0)
          & v3_pre_topc(sK6(X0),X0)
          & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v4_pre_topc(X2,X0)
            | ~ v3_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK6(X0),X0)
        & v3_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v4_pre_topc(X2,X0)
            | ~ v3_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f277,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f276,f85,f105])).

fof(f105,plain,
    ( spl8_3
  <=> r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f276,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(subsumption_resolution,[],[f194,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f194,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5)
    | ~ r1_tarski(sK5,sK5) ),
    inference(resolution,[],[f193,f50])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | r1_tarski(k2_pre_topc(sK4,sK5),X0)
      | ~ r1_tarski(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f190,f49])).

fof(f190,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK5,X0)
      | ~ v4_pre_topc(X0,sK4)
      | r1_tarski(k2_pre_topc(sK4,sK5),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ l1_pre_topc(sK4) ) ),
    inference(resolution,[],[f59,f50])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f236,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f223,f89])).

fof(f89,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f54,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f223,plain,
    ( v1_subset_1(sK5,sK5)
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f53,f188])).

fof(f188,plain,
    ( u1_struct_0(sK4) = sK5
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl8_9
  <=> u1_struct_0(sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f53,plain,(
    v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f218,plain,
    ( spl8_9
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f217,f153,f146,f186])).

fof(f146,plain,
    ( spl8_7
  <=> r1_tarski(u1_struct_0(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f153,plain,
    ( spl8_8
  <=> r1_tarski(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f217,plain,
    ( u1_struct_0(sK4) = sK5
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f216,f155])).

fof(f155,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f216,plain,
    ( u1_struct_0(sK4) = sK5
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | ~ spl8_7 ),
    inference(resolution,[],[f147,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f147,plain,
    ( r1_tarski(u1_struct_0(sK4),sK5)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f215,plain,
    ( spl8_7
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f214,f142,f105,f146])).

fof(f142,plain,
    ( spl8_6
  <=> v1_tops_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f214,plain,
    ( r1_tarski(u1_struct_0(sK4),sK5)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f213,f49])).

fof(f213,plain,
    ( r1_tarski(u1_struct_0(sK4),sK5)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f212,plain,
    ( r1_tarski(u1_struct_0(sK4),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f204,f143])).

fof(f143,plain,
    ( v1_tops_1(sK5,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f204,plain,
    ( r1_tarski(u1_struct_0(sK4),sK5)
    | ~ v1_tops_1(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ spl8_3 ),
    inference(superposition,[],[f106,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f106,plain,
    ( r1_tarski(k2_pre_topc(sK4,sK5),sK5)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f183,plain,
    ( spl8_6
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f182,f81,f142])).

fof(f182,plain,
    ( v1_tops_1(sK5,sK4)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f181,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f181,plain,
    ( v1_tops_1(sK5,sK4)
    | v2_struct_0(sK4)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f180,plain,
    ( v1_tops_1(sK5,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f173,f49])).

fof(f173,plain,
    ( v1_tops_1(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f172,f83])).

fof(f172,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | v1_tops_1(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f52,plain,(
    v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f169,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | ~ v3_pre_topc(sK5,sK4)
    | v1_tops_1(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f60,f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f156,plain,
    ( ~ spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f151,f153,f142])).

fof(f151,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4))
    | ~ v1_tops_1(sK5,sK4) ),
    inference(subsumption_resolution,[],[f150,f49])).

fof(f150,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4))
    | ~ v1_tops_1(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f134,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4))
    | ~ v1_tops_1(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(superposition,[],[f102,f57])).

fof(f102,plain,(
    r1_tarski(sK5,k2_pre_topc(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f99,plain,
    ( r1_tarski(sK5,k2_pre_topc(sK4,sK5))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f131,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f129,f49])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f128,plain,
    ( ~ v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f127,f47])).

fof(f127,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | spl8_5 ),
    inference(resolution,[],[f125,f93])).

fof(f93,plain,(
    ! [X1] :
      ( sP2(X1)
      | ~ v2_pre_topc(X1)
      | ~ v3_tdlat_3(X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | ~ v3_tdlat_3(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v3_tdlat_3(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f74,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f125,plain,
    ( ~ sP2(sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_5
  <=> sP2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f126,plain,
    ( ~ spl8_5
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f121,f85,f81,f123])).

fof(f121,plain,
    ( v3_pre_topc(sK5,sK4)
    | ~ sP2(sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f118,f87])).

fof(f87,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f118,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | v3_pre_topc(sK5,sK4)
    | ~ sP2(sK4) ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v3_pre_topc(X2,X0)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ( ~ v3_pre_topc(sK7(X0),X0)
          & v4_pre_topc(sK7(X0),X0)
          & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK7(X0),X0)
        & v4_pre_topc(sK7(X0),X0)
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f88,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f51,f85,f81])).

fof(f51,plain,
    ( v4_pre_topc(sK5,sK4)
    | v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3557)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (3549)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (3546)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (3549)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f88,f126,f131,f156,f183,f215,f218,f236,f277,f279,f284])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    spl8_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f283])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    $false | spl8_10),
% 0.20/0.49    inference(subsumption_resolution,[],[f282,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    l1_pre_topc(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    (v1_subset_1(sK5,u1_struct_0(sK4)) & v3_tex_2(sK5,sK4) & (v4_pre_topc(sK5,sK4) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f31,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK4)) & v3_tex_2(X1,sK4) & (v4_pre_topc(X1,sK4) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v3_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ? [X1] : (v1_subset_1(X1,u1_struct_0(sK4)) & v3_tex_2(X1,sK4) & (v4_pre_topc(X1,sK4) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => (v1_subset_1(sK5,u1_struct_0(sK4)) & v3_tex_2(sK5,sK4) & (v4_pre_topc(sK5,sK4) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    ~l1_pre_topc(sK4) | spl8_10),
% 0.20/0.49    inference(subsumption_resolution,[],[f281,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    v3_tdlat_3(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    ~v3_tdlat_3(sK4) | ~l1_pre_topc(sK4) | spl8_10),
% 0.20/0.49    inference(subsumption_resolution,[],[f280,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    v2_pre_topc(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f280,plain,(
% 0.20/0.49    ~v2_pre_topc(sK4) | ~v3_tdlat_3(sK4) | ~l1_pre_topc(sK4) | spl8_10),
% 0.20/0.49    inference(resolution,[],[f245,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X1] : (sP0(X1) | ~v2_pre_topc(X1) | ~v3_tdlat_3(X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.49    inference(resolution,[],[f67,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0] : (~sP1(X0) | ~v3_tdlat_3(X0) | sP0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (((v3_tdlat_3(X0) | ~sP0(X0)) & (sP0(X0) | ~v3_tdlat_3(X0))) | ~sP1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0] : (sP1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f21,f25,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (sP0(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    ~sP0(sK4) | spl8_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f243])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    spl8_10 <=> sP0(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    ~spl8_10 | spl8_2 | ~spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f278,f81,f85,f243])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl8_2 <=> v4_pre_topc(sK5,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl8_1 <=> v3_pre_topc(sK5,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    v4_pre_topc(sK5,sK4) | ~sP0(sK4) | ~spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    v3_pre_topc(sK5,sK4) | ~spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~v3_pre_topc(sK5,sK4) | v4_pre_topc(sK5,sK4) | ~sP0(sK4)),
% 0.20/0.49    inference(resolution,[],[f63,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | v4_pre_topc(X2,X0) | ~sP0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0] : ((sP0(X0) | (~v4_pre_topc(sK6(X0),X0) & v3_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK6(X0),X0) & v3_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0] : ((sP0(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.20/0.49    inference(rectify,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0] : ((sP0(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f24])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    spl8_3 | ~spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f276,f85,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl8_3 <=> r1_tarski(k2_pre_topc(sK4,sK5),sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    ~v4_pre_topc(sK5,sK4) | r1_tarski(k2_pre_topc(sK4,sK5),sK5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f194,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ~v4_pre_topc(sK5,sK4) | r1_tarski(k2_pre_topc(sK4,sK5),sK5) | ~r1_tarski(sK5,sK5)),
% 0.20/0.49    inference(resolution,[],[f193,f50])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | r1_tarski(k2_pre_topc(sK4,sK5),X0) | ~r1_tarski(sK5,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f190,f49])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK5,X0) | ~v4_pre_topc(X0,sK4) | r1_tarski(k2_pre_topc(sK4,sK5),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4)) )),
% 0.20/0.49    inference(resolution,[],[f59,f50])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_pre_topc(X0,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    ~spl8_9),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    $false | ~spl8_9),
% 0.20/0.49    inference(subsumption_resolution,[],[f223,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f54,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    v1_subset_1(sK5,sK5) | ~spl8_9),
% 0.20/0.49    inference(backward_demodulation,[],[f53,f188])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    u1_struct_0(sK4) = sK5 | ~spl8_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f186])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    spl8_9 <=> u1_struct_0(sK4) = sK5),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    v1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    spl8_9 | ~spl8_7 | ~spl8_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f217,f153,f146,f186])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl8_7 <=> r1_tarski(u1_struct_0(sK4),sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    spl8_8 <=> r1_tarski(sK5,u1_struct_0(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    u1_struct_0(sK4) = sK5 | (~spl8_7 | ~spl8_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f216,f155])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    r1_tarski(sK5,u1_struct_0(sK4)) | ~spl8_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f153])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    u1_struct_0(sK4) = sK5 | ~r1_tarski(sK5,u1_struct_0(sK4)) | ~spl8_7),
% 0.20/0.49    inference(resolution,[],[f147,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK4),sK5) | ~spl8_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f146])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    spl8_7 | ~spl8_3 | ~spl8_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f214,f142,f105,f146])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl8_6 <=> v1_tops_1(sK5,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK4),sK5) | (~spl8_3 | ~spl8_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f213,f49])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK4),sK5) | ~l1_pre_topc(sK4) | (~spl8_3 | ~spl8_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f212,f50])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK4),sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | (~spl8_3 | ~spl8_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f204,f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    v1_tops_1(sK5,sK4) | ~spl8_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f142])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK4),sK5) | ~v1_tops_1(sK5,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~spl8_3),
% 0.20/0.49    inference(superposition,[],[f106,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    r1_tarski(k2_pre_topc(sK4,sK5),sK5) | ~spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl8_6 | ~spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f182,f81,f142])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    v1_tops_1(sK5,sK4) | ~spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f181,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~v2_struct_0(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    v1_tops_1(sK5,sK4) | v2_struct_0(sK4) | ~spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f180,f47])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    v1_tops_1(sK5,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f173,f49])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    v1_tops_1(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f172,f83])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ~v3_pre_topc(sK5,sK4) | v1_tops_1(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    v3_tex_2(sK5,sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ~v3_tex_2(sK5,sK4) | ~v3_pre_topc(sK5,sK4) | v1_tops_1(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.20/0.49    inference(resolution,[],[f60,f50])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    ~spl8_6 | spl8_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f151,f153,f142])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    r1_tarski(sK5,u1_struct_0(sK4)) | ~v1_tops_1(sK5,sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f150,f49])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    r1_tarski(sK5,u1_struct_0(sK4)) | ~v1_tops_1(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f50])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    r1_tarski(sK5,u1_struct_0(sK4)) | ~v1_tops_1(sK5,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4)),
% 0.20/0.49    inference(superposition,[],[f102,f57])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    r1_tarski(sK5,k2_pre_topc(sK4,sK5))),
% 0.20/0.49    inference(subsumption_resolution,[],[f99,f49])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    r1_tarski(sK5,k2_pre_topc(sK4,sK5)) | ~l1_pre_topc(sK4)),
% 0.20/0.49    inference(resolution,[],[f56,f50])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl8_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    $false | spl8_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f49])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ~l1_pre_topc(sK4) | spl8_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f128,f48])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ~v3_tdlat_3(sK4) | ~l1_pre_topc(sK4) | spl8_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f127,f47])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~v2_pre_topc(sK4) | ~v3_tdlat_3(sK4) | ~l1_pre_topc(sK4) | spl8_5),
% 0.20/0.49    inference(resolution,[],[f125,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X1] : (sP2(X1) | ~v2_pre_topc(X1) | ~v3_tdlat_3(X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.49    inference(resolution,[],[f74,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0] : (~sP3(X0) | ~v3_tdlat_3(X0) | sP2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0] : (((v3_tdlat_3(X0) | ~sP2(X0)) & (sP2(X0) | ~v3_tdlat_3(X0))) | ~sP3(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> sP2(X0)) | ~sP3(X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0] : (sP3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (sP3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f23,f28,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (sP2(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ~sP2(sK4) | spl8_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl8_5 <=> sP2(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ~spl8_5 | spl8_1 | ~spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f121,f85,f81,f123])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    v3_pre_topc(sK5,sK4) | ~sP2(sK4) | ~spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    v4_pre_topc(sK5,sK4) | ~spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ~v4_pre_topc(sK5,sK4) | v3_pre_topc(sK5,sK4) | ~sP2(sK4)),
% 0.20/0.49    inference(resolution,[],[f70,f50])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~sP2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0] : ((sP2(X0) | (~v3_pre_topc(sK7(X0),X0) & v4_pre_topc(sK7(X0),X0) & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK7(X0),X0) & v4_pre_topc(sK7(X0),X0) & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0] : ((sP2(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0)))),
% 0.20/0.49    inference(rectify,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0] : ((sP2(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f27])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl8_1 | spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f85,f81])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    v4_pre_topc(sK5,sK4) | v3_pre_topc(sK5,sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (3549)------------------------------
% 0.20/0.49  % (3549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3549)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (3549)Memory used [KB]: 6268
% 0.20/0.49  % (3549)Time elapsed: 0.096 s
% 0.20/0.49  % (3549)------------------------------
% 0.20/0.49  % (3549)------------------------------
% 0.20/0.50  % (3542)Success in time 0.139 s
%------------------------------------------------------------------------------
