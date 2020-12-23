%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 251 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  308 (1360 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f83,f102,f105,f129,f135,f162,f169,f171,f173,f180,f256])).

fof(f256,plain,
    ( ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f186,f54])).

fof(f54,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f32,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f186,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f27,f184])).

fof(f184,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f82,f66])).

fof(f66,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_3
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f82,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_5
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f27,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f180,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f179,f78,f51])).

fof(f51,plain,
    ( spl3_2
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f179,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f110])).

fof(f110,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f28,f29,f31,f26,f106])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f40,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
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

fof(f26,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f173,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f155,f25])).

fof(f155,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f171,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f161,f29])).

fof(f161,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f169,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f158,f30])).

fof(f30,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f158,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_12
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f162,plain,
    ( spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f151,f90,f160,f119,f157,f154,f51])).

fof(f119,plain,
    ( spl3_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f90,plain,
    ( spl3_6
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f151,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f138,f104])).

fof(f104,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(resolution,[],[f97,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f135,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f132,f25])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(resolution,[],[f94,f45])).

fof(f94,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f120,f31])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f105,plain,
    ( spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f103,f93,f90])).

fof(f103,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f31,f100,f84])).

fof(f84,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f38,f55])).

fof(f55,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f46,f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f100,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f24,f29,f30,f31,f96])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f41,f25])).

fof(f24,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f76,f81,f78])).

fof(f76,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f31,f72])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f37,f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f68,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f63,f48,f65])).

fof(f63,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(global_subsumption,[],[f31,f59])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f35,f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (2841)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.46  % (2841)Refutation not found, incomplete strategy% (2841)------------------------------
% 0.21/0.46  % (2841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (2841)Memory used [KB]: 10618
% 0.21/0.46  % (2841)Time elapsed: 0.046 s
% 0.21/0.46  % (2841)------------------------------
% 0.21/0.46  % (2841)------------------------------
% 0.21/0.46  % (2849)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (2843)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (2839)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (2839)Refutation not found, incomplete strategy% (2839)------------------------------
% 0.21/0.49  % (2839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2839)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2839)Memory used [KB]: 10618
% 0.21/0.49  % (2839)Time elapsed: 0.076 s
% 0.21/0.49  % (2839)------------------------------
% 0.21/0.49  % (2839)------------------------------
% 0.21/0.49  % (2840)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (2843)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f68,f83,f102,f105,f129,f135,f162,f169,f171,f173,f180,f256])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    $false | (~spl3_3 | ~spl3_5)),
% 0.21/0.49    inference(resolution,[],[f186,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f32,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    v1_subset_1(sK1,sK1) | (~spl3_3 | ~spl3_5)),
% 0.21/0.49    inference(backward_demodulation,[],[f27,f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK0) | (~spl3_3 | ~spl3_5)),
% 0.21/0.49    inference(forward_demodulation,[],[f82,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_3 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_5 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~spl3_2 | spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f179,f78,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_2 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    v1_tops_1(sK1,sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f28,f29,f31,f26,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f40,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl3_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    $false | spl3_11),
% 0.21/0.49    inference(resolution,[],[f155,f25])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl3_11 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl3_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    $false | spl3_13),
% 0.21/0.49    inference(resolution,[],[f161,f29])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl3_13 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    $false | spl3_12),
% 0.21/0.49    inference(resolution,[],[f158,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v3_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~v3_tdlat_3(sK0) | spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl3_12 <=> v3_tdlat_3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_8 | ~spl3_13 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f151,f90,f160,f119,f157,f154,f51])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl3_8 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_6 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | ~spl3_6),
% 0.21/0.49    inference(resolution,[],[f138,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(resolution,[],[f97,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(resolution,[],[f41,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    $false | spl3_7),
% 0.21/0.49    inference(resolution,[],[f132,f25])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 0.21/0.49    inference(resolution,[],[f94,f45])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl3_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    $false | spl3_8),
% 0.21/0.49    inference(resolution,[],[f120,f31])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_6 | ~spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f103,f93,f90])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f31,f100,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(superposition,[],[f38,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.49    inference(resolution,[],[f46,f25])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f24,f29,f30,f31,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.49    inference(resolution,[],[f41,f25])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    $false | spl3_1),
% 0.21/0.49    inference(resolution,[],[f100,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl3_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~spl3_4 | spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f81,f78])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f31,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f37,f25])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl3_3 | ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f48,f65])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    inference(global_subsumption,[],[f31,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f35,f25])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (2843)------------------------------
% 0.21/0.49  % (2843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2843)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (2843)Memory used [KB]: 10746
% 0.21/0.49  % (2843)Time elapsed: 0.081 s
% 0.21/0.49  % (2843)------------------------------
% 0.21/0.49  % (2843)------------------------------
% 0.21/0.49  % (2830)Success in time 0.135 s
%------------------------------------------------------------------------------
