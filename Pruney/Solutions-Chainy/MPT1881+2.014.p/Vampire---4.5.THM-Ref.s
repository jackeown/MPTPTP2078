%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 385 expanded)
%              Number of leaves         :   45 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :  753 (1587 expanded)
%              Number of equality atoms :   64 ( 136 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f94,f98,f102,f106,f110,f114,f123,f129,f133,f144,f175,f202,f205,f212,f281,f283,f297,f316,f324,f329,f355,f357,f358,f364,f373,f380,f381])).

fof(f381,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | sK1 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f380,plain,
    ( ~ spl3_4
    | spl3_19
    | ~ spl3_14
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f379,f210,f141,f121,f169,f199,f100])).

fof(f100,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f199,plain,
    ( spl3_19
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f169,plain,
    ( spl3_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f121,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f141,plain,
    ( spl3_11
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f210,plain,
    ( spl3_20
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f379,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f378,f142])).

fof(f142,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f378,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f377,f122])).

fof(f122,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f377,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( sK1 != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f375,f142])).

fof(f375,plain,
    ( sK1 != k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f374,f122])).

fof(f374,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f235,f142])).

fof(f235,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20 ),
    inference(superposition,[],[f70,f211])).

fof(f211,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f70,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f373,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_8
    | ~ spl3_11
    | spl3_36 ),
    inference(avatar_split_clause,[],[f372,f362,f141,f121,f169,f100,f104,f108,f112])).

fof(f112,plain,
    ( spl3_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f108,plain,
    ( spl3_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f104,plain,
    ( spl3_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f362,plain,
    ( spl3_36
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f372,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | spl3_36 ),
    inference(forward_demodulation,[],[f371,f142])).

fof(f371,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | spl3_36 ),
    inference(forward_demodulation,[],[f370,f122])).

fof(f370,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_36 ),
    inference(resolution,[],[f363,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f363,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f362])).

fof(f364,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_4
    | spl3_1
    | ~ spl3_36
    | ~ spl3_14
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f360,f199,f141,f121,f169,f362,f86,f100,f108,f112])).

fof(f86,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f359,f142])).

fof(f359,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f231,f122])).

fof(f231,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_19 ),
    inference(resolution,[],[f200,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f200,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f358,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f357,plain,(
    ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl3_35 ),
    inference(resolution,[],[f354,f116])).

fof(f116,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(global_subsumption,[],[f115,f84])).

fof(f84,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f115,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f354,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl3_35
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f355,plain,
    ( spl3_35
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f344,f141,f131,f353])).

fof(f131,plain,
    ( spl3_10
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f344,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(superposition,[],[f143,f142])).

fof(f143,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f329,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | sK1 = k2_struct_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f324,plain,
    ( spl3_32
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f318,f314,f127,f322])).

fof(f322,plain,
    ( spl3_32
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f127,plain,
    ( spl3_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f314,plain,
    ( spl3_31
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f318,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(resolution,[],[f315,f128])).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f315,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1 )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f314])).

fof(f316,plain,
    ( ~ spl3_4
    | spl3_31
    | ~ spl3_8
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f312,f295,f121,f314,f100])).

fof(f295,plain,
    ( spl3_29
  <=> ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f312,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_29 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f303,f122])).

fof(f303,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_29 ),
    inference(resolution,[],[f301,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f301,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_29 ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_29 ),
    inference(resolution,[],[f296,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | ~ spl3_5
    | spl3_29
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f293,f279,f121,f295,f104,f100,f108])).

fof(f279,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f292,f122])).

fof(f292,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_27 ),
    inference(resolution,[],[f286,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f286,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(superposition,[],[f280,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f280,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f279])).

fof(f283,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl3_26 ),
    inference(resolution,[],[f277,f115])).

fof(f277,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl3_26
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f281,plain,
    ( ~ spl3_26
    | spl3_27
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f269,f121,f100,f279,f276])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f190,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f189,f122])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f151,f122])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f72,f101])).

fof(f101,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f212,plain,
    ( ~ spl3_4
    | spl3_20
    | ~ spl3_9
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f208,f199,f121,f127,f210,f100])).

fof(f208,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f207,f122])).

fof(f207,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f206,f122])).

fof(f206,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_19 ),
    inference(resolution,[],[f200,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f205,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_8
    | spl3_18 ),
    inference(avatar_split_clause,[],[f204,f196,f121,f127,f104,f100,f108])).

fof(f196,plain,
    ( spl3_18
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f204,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_8
    | spl3_18 ),
    inference(forward_demodulation,[],[f203,f122])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_18 ),
    inference(resolution,[],[f197,f76])).

fof(f197,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f202,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_4
    | ~ spl3_18
    | spl3_19
    | ~ spl3_9
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f193,f121,f86,f127,f199,f196,f100,f108,f112])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f192,f122])).

fof(f192,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f92,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f92,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f175,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | sK1 != k2_struct_0(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f144,plain,
    ( spl3_11
    | spl3_10
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f139,f121,f96,f131,f141])).

fof(f96,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f139,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f138,f122])).

fof(f138,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f134,f122])).

fof(f134,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f82,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f133,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f125,f121,f89,f131])).

fof(f89,plain,
    ( spl3_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f125,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f93,f122])).

fof(f93,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f129,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f124,f121,f96,f127])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f97,f122])).

fof(f123,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f119,f100,f121])).

fof(f119,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f118,f101])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f64,f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f114,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f54,f112])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f110,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f55,f108])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f56,f104])).

fof(f56,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f57,f100])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f58,f96])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f89,f86])).

fof(f59,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f60,f89,f86])).

fof(f60,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (9122)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (9124)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (9113)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (9129)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (9128)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (9120)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (9131)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (9133)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (9117)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9120)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f382,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f91,f94,f98,f102,f106,f110,f114,f123,f129,f133,f144,f175,f202,f205,f212,f281,f283,f297,f316,f324,f329,f355,f357,f358,f364,f373,f380,f381])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    sK1 != k2_pre_topc(sK0,sK1) | sK1 != k2_struct_0(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f380,plain,(
% 0.22/0.53    ~spl3_4 | spl3_19 | ~spl3_14 | ~spl3_8 | ~spl3_11 | ~spl3_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f379,f210,f141,f121,f169,f199,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    spl3_19 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    spl3_14 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl3_11 <=> sK1 = k2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    spl3_20 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_11 | ~spl3_20)),
% 0.22/0.53    inference(forward_demodulation,[],[f378,f142])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    sK1 = k2_struct_0(sK0) | ~spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f141])).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_11 | ~spl3_20)),
% 0.22/0.53    inference(forward_demodulation,[],[f377,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f121])).
% 0.22/0.53  fof(f377,plain,(
% 0.22/0.53    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_11 | ~spl3_20)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f376])).
% 0.22/0.53  fof(f376,plain,(
% 0.22/0.53    sK1 != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_11 | ~spl3_20)),
% 0.22/0.53    inference(forward_demodulation,[],[f375,f142])).
% 0.22/0.53  fof(f375,plain,(
% 0.22/0.53    sK1 != k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_11 | ~spl3_20)),
% 0.22/0.53    inference(forward_demodulation,[],[f374,f122])).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    u1_struct_0(sK0) != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_11 | ~spl3_20)),
% 0.22/0.53    inference(forward_demodulation,[],[f235,f142])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_20),
% 0.22/0.53    inference(superposition,[],[f70,f211])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f210])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.22/0.53  fof(f373,plain,(
% 0.22/0.53    spl3_7 | ~spl3_6 | ~spl3_5 | ~spl3_4 | ~spl3_14 | ~spl3_8 | ~spl3_11 | spl3_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f372,f362,f141,f121,f169,f100,f104,f108,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl3_7 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl3_6 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl3_5 <=> v1_tdlat_3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f362,plain,(
% 0.22/0.53    spl3_36 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_11 | spl3_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f371,f142])).
% 0.22/0.53  fof(f371,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | spl3_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f370,f122])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl3_36),
% 0.22/0.53    inference(resolution,[],[f363,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    ~v2_tex_2(sK1,sK0) | spl3_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f362])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    spl3_7 | ~spl3_6 | ~spl3_4 | spl3_1 | ~spl3_36 | ~spl3_14 | ~spl3_8 | ~spl3_11 | ~spl3_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f360,f199,f141,f121,f169,f362,f86,f100,f108,f112])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f360,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_11 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f359,f142])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f231,f122])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_19),
% 0.22/0.53    inference(resolution,[],[f200,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    v1_tops_1(sK1,sK0) | ~spl3_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f199])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f357,plain,(
% 0.22/0.53    ~spl3_35),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f356])).
% 0.22/0.53  fof(f356,plain,(
% 0.22/0.53    $false | ~spl3_35),
% 0.22/0.53    inference(resolution,[],[f354,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.22/0.53    inference(global_subsumption,[],[f115,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f63,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.53  fof(f354,plain,(
% 0.22/0.53    v1_subset_1(sK1,sK1) | ~spl3_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f353])).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    spl3_35 <=> v1_subset_1(sK1,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    spl3_35 | ~spl3_10 | ~spl3_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f344,f141,f131,f353])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    spl3_10 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f344,plain,(
% 0.22/0.53    v1_subset_1(sK1,sK1) | (~spl3_10 | ~spl3_11)),
% 0.22/0.53    inference(superposition,[],[f143,f142])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f131])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    sK1 != k2_pre_topc(sK0,sK1) | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | sK1 = k2_struct_0(sK0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    spl3_32 | ~spl3_9 | ~spl3_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f318,f314,f127,f322])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    spl3_32 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl3_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    spl3_31 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.53  fof(f318,plain,(
% 0.22/0.53    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_9 | ~spl3_31)),
% 0.22/0.53    inference(resolution,[],[f315,f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f127])).
% 0.22/0.53  fof(f315,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1) ) | ~spl3_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f314])).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    ~spl3_4 | spl3_31 | ~spl3_8 | ~spl3_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f312,f295,f121,f314,f100])).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    spl3_29 <=> ! [X0] : (~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1 | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_29)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f311])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1 | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_29)),
% 0.22/0.53    inference(forward_demodulation,[],[f303,f122])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_29),
% 0.22/0.53    inference(resolution,[],[f301,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_29),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f300])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_29),
% 0.22/0.53    inference(resolution,[],[f296,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl3_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f295])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    ~spl3_6 | ~spl3_4 | ~spl3_5 | spl3_29 | ~spl3_8 | ~spl3_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f293,f279,f121,f295,f104,f100,f108])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    spl3_27 <=> ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.53  fof(f293,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_27)),
% 0.22/0.53    inference(forward_demodulation,[],[f292,f122])).
% 0.22/0.53  fof(f292,plain,(
% 0.22/0.53    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_27),
% 0.22/0.53    inference(resolution,[],[f286,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(rectify,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_27),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f285])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_27),
% 0.22/0.53    inference(superposition,[],[f280,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_27),
% 0.22/0.53    inference(avatar_component_clause,[],[f279])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    spl3_26),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f282])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    $false | spl3_26),
% 0.22/0.53    inference(resolution,[],[f277,f115])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_26),
% 0.22/0.53    inference(avatar_component_clause,[],[f276])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    spl3_26 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    ~spl3_26 | spl3_27 | ~spl3_4 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f269,f121,f100,f279,f276])).
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_4 | ~spl3_8)),
% 0.22/0.53    inference(superposition,[],[f190,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f189,f122])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f151,f122])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl3_4),
% 0.22/0.53    inference(resolution,[],[f72,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f100])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    ~spl3_4 | spl3_20 | ~spl3_9 | ~spl3_8 | ~spl3_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f208,f199,f121,f127,f210,f100])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f207,f122])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f206,f122])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_19),
% 0.22/0.53    inference(resolution,[],[f200,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ~spl3_6 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_8 | spl3_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f204,f196,f121,f127,f104,f100,f108])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    spl3_18 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_8 | spl3_18)),
% 0.22/0.53    inference(forward_demodulation,[],[f203,f122])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_18),
% 0.22/0.53    inference(resolution,[],[f197,f76])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ~v3_pre_topc(sK1,sK0) | spl3_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f196])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    spl3_7 | ~spl3_6 | ~spl3_4 | ~spl3_18 | spl3_19 | ~spl3_9 | ~spl3_1 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f193,f121,f86,f127,f199,f196,f100,f108,f112])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_1 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f192,f122])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    v1_tops_1(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f92,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | v1_tops_1(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    v3_tex_2(sK1,sK0) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | sK1 != k2_struct_0(sK0) | m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    spl3_11 | spl3_10 | ~spl3_3 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f139,f121,f96,f131,f141])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0) | (~spl3_3 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f138,f122])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_3 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f134,f122])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.22/0.53    inference(resolution,[],[f82,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ~spl3_10 | spl3_2 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f125,f121,f89,f131])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~v1_subset_1(sK1,k2_struct_0(sK0)) | (spl3_2 | ~spl3_8)),
% 0.22/0.53    inference(superposition,[],[f93,f122])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl3_9 | ~spl3_3 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f124,f121,f96,f127])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_8)),
% 0.22/0.53    inference(superposition,[],[f97,f122])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl3_8 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f119,f100,f121])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_4),
% 0.22/0.53    inference(resolution,[],[f118,f101])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f64,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f112])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f18])).
% 0.22/0.53  fof(f18,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f108])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f104])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    v1_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f100])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f96])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f89,f86])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ~spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f60,f89,f86])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (9120)------------------------------
% 0.22/0.53  % (9120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9120)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (9120)Memory used [KB]: 10874
% 0.22/0.53  % (9120)Time elapsed: 0.084 s
% 0.22/0.53  % (9120)------------------------------
% 0.22/0.53  % (9120)------------------------------
% 0.22/0.53  % (9126)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9106)Success in time 0.169 s
%------------------------------------------------------------------------------
