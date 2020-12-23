%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:37 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 364 expanded)
%              Number of leaves         :   36 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  828 (1460 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f153,f155,f160,f171,f188,f200,f225,f236,f244,f263,f307,f333,f349,f369,f372,f380])).

fof(f380,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f378,f93])).

fof(f93,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f378,plain,
    ( v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f377,f148])).

fof(f148,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_8
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f377,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_9
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f376,f159])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f376,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f375,f151])).

fof(f151,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_9
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f375,plain,
    ( v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(superposition,[],[f364,f126])).

fof(f126,plain,
    ( ! [X2] :
        ( u1_struct_0(sK3(sK0,X2)) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK0)
        | v1_xboole_0(X2) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f125,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK0)
        | u1_struct_0(sK3(sK0,X2)) = X2 )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f117,f103])).

fof(f103,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f117,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK0)
        | u1_struct_0(sK3(sK0,X2)) = X2 )
    | spl6_2 ),
    inference(resolution,[],[f98,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f98,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f364,plain,
    ( v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl6_28
  <=> v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f372,plain,
    ( ~ spl6_15
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl6_15
    | spl6_29 ),
    inference(subsumption_resolution,[],[f370,f208])).

fof(f208,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl6_15
  <=> l1_pre_topc(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f370,plain,
    ( ~ l1_pre_topc(sK3(sK0,sK1))
    | spl6_29 ),
    inference(resolution,[],[f368,f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f368,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl6_29
  <=> l1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f369,plain,
    ( spl6_28
    | ~ spl6_29
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f350,f218,f366,f362])).

fof(f218,plain,
    ( spl6_17
  <=> v7_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f350,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))
    | ~ spl6_17 ),
    inference(resolution,[],[f220,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f220,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f218])).

fof(f349,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | spl6_18 ),
    inference(subsumption_resolution,[],[f347,f98])).

fof(f347,plain,
    ( v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | spl6_18 ),
    inference(subsumption_resolution,[],[f346,f148])).

fof(f346,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | spl6_18 ),
    inference(subsumption_resolution,[],[f345,f159])).

fof(f345,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f344,f93])).

fof(f344,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f343,f113])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_18 ),
    inference(subsumption_resolution,[],[f342,f103])).

fof(f342,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_18 ),
    inference(resolution,[],[f224,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK3(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f224,plain,
    ( ~ v1_tdlat_3(sK3(sK0,sK1))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl6_18
  <=> v1_tdlat_3(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f333,plain,
    ( spl6_1
    | ~ spl6_10
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl6_1
    | ~ spl6_10
    | spl6_23 ),
    inference(subsumption_resolution,[],[f331,f93])).

fof(f331,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_10
    | spl6_23 ),
    inference(subsumption_resolution,[],[f330,f159])).

fof(f330,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | spl6_23 ),
    inference(resolution,[],[f308,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_23 ),
    inference(resolution,[],[f306,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f306,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl6_23
  <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f307,plain,
    ( ~ spl6_23
    | spl6_8
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f299,f260,f186,f146,f304])).

fof(f186,plain,
    ( spl6_13
  <=> ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f260,plain,
    ( spl6_19
  <=> sK1 = k1_tarski(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f299,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | spl6_8
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f296,f147])).

fof(f147,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f296,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(superposition,[],[f187,f262])).

fof(f262,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f260])).

fof(f187,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f263,plain,
    ( spl6_19
    | spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f255,f150,f91,f260])).

fof(f255,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f253,f93])).

fof(f253,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | v1_xboole_0(sK1)
    | spl6_1
    | ~ spl6_9 ),
    inference(resolution,[],[f250,f79])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | k1_tarski(X1) = sK1 )
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f247,f61])).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f247,plain,
    ( ! [X1] :
        ( k1_tarski(X1) = sK1
        | v1_xboole_0(k1_tarski(X1))
        | ~ r2_hidden(X1,sK1) )
    | spl6_1
    | ~ spl6_9 ),
    inference(resolution,[],[f242,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f242,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | sK1 = X2
        | v1_xboole_0(X2) )
    | spl6_1
    | ~ spl6_9 ),
    inference(resolution,[],[f240,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v1_xboole_0(X0)
        | sK1 = X0 )
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f239,f93])).

fof(f239,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X0,sK1)
        | sK1 = X0 )
    | ~ spl6_9 ),
    inference(resolution,[],[f152,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f152,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f244,plain,
    ( ~ spl6_8
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(avatar_split_clause,[],[f237,f207,f157,f111,f101,f96,f91,f146])).

fof(f237,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(subsumption_resolution,[],[f228,f93])).

fof(f228,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(subsumption_resolution,[],[f227,f159])).

fof(f227,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_15 ),
    inference(subsumption_resolution,[],[f226,f113])).

fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_15 ),
    inference(resolution,[],[f215,f124])).

fof(f124,plain,
    ( ! [X1] :
        ( m1_pre_topc(sK3(sK0,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v1_xboole_0(X1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f123,f113])).

fof(f123,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | m1_pre_topc(sK3(sK0,X1),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f116,f103])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | m1_pre_topc(sK3(sK0,X1),sK0) )
    | spl6_2 ),
    inference(resolution,[],[f98,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl6_15 ),
    inference(resolution,[],[f209,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f209,plain,
    ( ~ l1_pre_topc(sK3(sK0,sK1))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f207])).

fof(f236,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | spl6_16 ),
    inference(subsumption_resolution,[],[f234,f159])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f233,f93])).

fof(f233,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f232,f148])).

fof(f232,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_16 ),
    inference(resolution,[],[f213,f172])).

fof(f172,plain,
    ( ! [X0] :
        ( v2_tdlat_3(sK3(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f124,f131])).

fof(f131,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK0)
        | v2_tdlat_3(X4) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f130,f113])).

fof(f130,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X4,sK0)
        | v2_tdlat_3(X4) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f129,f108])).

fof(f108,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_4
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f129,plain,
    ( ! [X4] :
        ( ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X4,sK0)
        | v2_tdlat_3(X4) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f119,f103])).

fof(f119,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X4,sK0)
        | v2_tdlat_3(X4) )
    | spl6_2 ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f213,plain,
    ( ~ v2_tdlat_3(sK3(sK0,sK1))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl6_16
  <=> v2_tdlat_3(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f225,plain,
    ( spl6_17
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_15
    | spl6_11 ),
    inference(avatar_split_clause,[],[f180,f168,f207,f222,f211,f218])).

fof(f168,plain,
    ( spl6_11
  <=> v2_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | ~ v2_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | spl6_11 ),
    inference(subsumption_resolution,[],[f178,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f178,plain,
    ( ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | ~ v2_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | spl6_11 ),
    inference(resolution,[],[f170,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f170,plain,
    ( ~ v2_struct_0(sK3(sK0,sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f200,plain,
    ( spl6_1
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f196,f93])).

fof(f196,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f190,f159])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1) )
    | ~ spl6_12 ),
    inference(resolution,[],[f184,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f184,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_12
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f188,plain,
    ( spl6_12
    | spl6_13
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f162,f111,f101,f96,f186,f182])).

fof(f162,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f128,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f128,plain,
    ( ! [X3] :
        ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X3),sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f127,f113])).

fof(f127,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X3),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f118,f103])).

fof(f118,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X3),sK0) )
    | spl6_2 ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f171,plain,
    ( ~ spl6_11
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f166,f157,f146,f111,f101,f96,f91,f168])).

fof(f166,plain,
    ( ~ v2_struct_0(sK3(sK0,sK1))
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f165,f93])).

fof(f165,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f163,f159])).

fof(f163,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f122,f148])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v2_struct_0(sK3(sK0,X0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f121,f113])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_struct_0(sK3(sK0,X0)) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f115,f103])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_struct_0(sK3(sK0,X0)) )
    | spl6_2 ),
    inference(resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f160,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f56,f157])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f155,plain,
    ( ~ spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f154,f146,f150])).

fof(f154,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f54,f148])).

fof(f54,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f153,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f53,f150,f146])).

fof(f53,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f60,f111])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f59,f106])).

fof(f59,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f57,f96])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:08:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (20546)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (20545)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (20556)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (20548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (20541)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20547)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20561)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (20543)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (20543)Refutation not found, incomplete strategy% (20543)------------------------------
% 0.22/0.55  % (20543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20543)Memory used [KB]: 10746
% 0.22/0.55  % (20543)Time elapsed: 0.125 s
% 0.22/0.55  % (20543)------------------------------
% 0.22/0.55  % (20543)------------------------------
% 0.22/0.55  % (20566)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (20563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  % (20551)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.55  % (20564)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.55  % (20565)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.55  % (20569)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.55  % (20544)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.44/0.55  % (20568)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (20554)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.56  % (20552)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.56  % (20557)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.56  % (20570)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.56  % (20542)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.56  % (20553)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.56  % (20555)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.56  % (20567)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.56  % (20560)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.56  % (20549)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (20562)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.57  % (20558)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.57  % (20563)Refutation not found, incomplete strategy% (20563)------------------------------
% 1.59/0.57  % (20563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (20563)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (20563)Memory used [KB]: 10746
% 1.59/0.57  % (20563)Time elapsed: 0.127 s
% 1.59/0.57  % (20563)------------------------------
% 1.59/0.57  % (20563)------------------------------
% 1.59/0.57  % (20559)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.57  % (20550)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.58  % (20561)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f381,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f153,f155,f160,f171,f188,f200,f225,f236,f244,f263,f307,f333,f349,f369,f372,f380])).
% 1.59/0.58  fof(f380,plain,(
% 1.59/0.58    spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_28),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f379])).
% 1.59/0.58  fof(f379,plain,(
% 1.59/0.58    $false | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_28)),
% 1.59/0.58    inference(subsumption_resolution,[],[f378,f93])).
% 1.59/0.58  fof(f93,plain,(
% 1.59/0.58    ~v1_xboole_0(sK1) | spl6_1),
% 1.59/0.58    inference(avatar_component_clause,[],[f91])).
% 1.59/0.58  fof(f91,plain,(
% 1.59/0.58    spl6_1 <=> v1_xboole_0(sK1)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.59/0.58  fof(f378,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_28)),
% 1.59/0.58    inference(subsumption_resolution,[],[f377,f148])).
% 1.59/0.58  fof(f148,plain,(
% 1.59/0.58    v2_tex_2(sK1,sK0) | ~spl6_8),
% 1.59/0.58    inference(avatar_component_clause,[],[f146])).
% 1.59/0.58  fof(f146,plain,(
% 1.59/0.58    spl6_8 <=> v2_tex_2(sK1,sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.59/0.58  fof(f377,plain,(
% 1.59/0.58    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | spl6_9 | ~spl6_10 | ~spl6_28)),
% 1.59/0.58    inference(subsumption_resolution,[],[f376,f159])).
% 1.59/0.58  fof(f159,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 1.59/0.58    inference(avatar_component_clause,[],[f157])).
% 1.59/0.58  fof(f157,plain,(
% 1.59/0.58    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.59/0.58  fof(f376,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | spl6_9 | ~spl6_28)),
% 1.59/0.58    inference(subsumption_resolution,[],[f375,f151])).
% 1.59/0.58  fof(f151,plain,(
% 1.59/0.58    ~v1_zfmisc_1(sK1) | spl6_9),
% 1.59/0.58    inference(avatar_component_clause,[],[f150])).
% 1.59/0.58  fof(f150,plain,(
% 1.59/0.58    spl6_9 <=> v1_zfmisc_1(sK1)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.59/0.58  fof(f375,plain,(
% 1.59/0.58    v1_zfmisc_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_28)),
% 1.59/0.58    inference(superposition,[],[f364,f126])).
% 1.59/0.58  fof(f126,plain,(
% 1.59/0.58    ( ! [X2] : (u1_struct_0(sK3(sK0,X2)) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X2,sK0) | v1_xboole_0(X2)) ) | (spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.59/0.58    inference(subsumption_resolution,[],[f125,f113])).
% 1.59/0.58  fof(f113,plain,(
% 1.59/0.58    l1_pre_topc(sK0) | ~spl6_5),
% 1.59/0.58    inference(avatar_component_clause,[],[f111])).
% 1.59/0.58  fof(f111,plain,(
% 1.59/0.58    spl6_5 <=> l1_pre_topc(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.59/0.58  fof(f125,plain,(
% 1.59/0.58    ( ! [X2] : (~l1_pre_topc(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X2,sK0) | u1_struct_0(sK3(sK0,X2)) = X2) ) | (spl6_2 | ~spl6_3)),
% 1.59/0.58    inference(subsumption_resolution,[],[f117,f103])).
% 1.59/0.58  fof(f103,plain,(
% 1.59/0.58    v2_pre_topc(sK0) | ~spl6_3),
% 1.59/0.58    inference(avatar_component_clause,[],[f101])).
% 1.59/0.58  fof(f101,plain,(
% 1.59/0.58    spl6_3 <=> v2_pre_topc(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.59/0.58  fof(f117,plain,(
% 1.59/0.58    ( ! [X2] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X2,sK0) | u1_struct_0(sK3(sK0,X2)) = X2) ) | spl6_2),
% 1.59/0.58    inference(resolution,[],[f98,f77])).
% 1.59/0.58  fof(f77,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f42,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f19])).
% 1.59/0.58  fof(f19,axiom,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 1.59/0.58  fof(f98,plain,(
% 1.59/0.58    ~v2_struct_0(sK0) | spl6_2),
% 1.59/0.58    inference(avatar_component_clause,[],[f96])).
% 1.59/0.58  fof(f96,plain,(
% 1.59/0.58    spl6_2 <=> v2_struct_0(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.59/0.58  fof(f364,plain,(
% 1.59/0.58    v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) | ~spl6_28),
% 1.59/0.58    inference(avatar_component_clause,[],[f362])).
% 1.59/0.58  fof(f362,plain,(
% 1.59/0.58    spl6_28 <=> v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.59/0.58  fof(f372,plain,(
% 1.59/0.58    ~spl6_15 | spl6_29),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f371])).
% 1.59/0.58  fof(f371,plain,(
% 1.59/0.58    $false | (~spl6_15 | spl6_29)),
% 1.59/0.58    inference(subsumption_resolution,[],[f370,f208])).
% 1.59/0.58  fof(f208,plain,(
% 1.59/0.58    l1_pre_topc(sK3(sK0,sK1)) | ~spl6_15),
% 1.59/0.58    inference(avatar_component_clause,[],[f207])).
% 1.59/0.58  fof(f207,plain,(
% 1.59/0.58    spl6_15 <=> l1_pre_topc(sK3(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.59/0.58  fof(f370,plain,(
% 1.59/0.58    ~l1_pre_topc(sK3(sK0,sK1)) | spl6_29),
% 1.59/0.58    inference(resolution,[],[f368,f65])).
% 1.59/0.58  fof(f65,plain,(
% 1.59/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f28])).
% 1.59/0.58  fof(f28,plain,(
% 1.59/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f10])).
% 1.59/0.58  fof(f10,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.59/0.58  fof(f368,plain,(
% 1.59/0.58    ~l1_struct_0(sK3(sK0,sK1)) | spl6_29),
% 1.59/0.58    inference(avatar_component_clause,[],[f366])).
% 1.59/0.58  fof(f366,plain,(
% 1.59/0.58    spl6_29 <=> l1_struct_0(sK3(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.59/0.58  fof(f369,plain,(
% 1.59/0.58    spl6_28 | ~spl6_29 | ~spl6_17),
% 1.59/0.58    inference(avatar_split_clause,[],[f350,f218,f366,f362])).
% 1.59/0.58  fof(f218,plain,(
% 1.59/0.58    spl6_17 <=> v7_struct_0(sK3(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.59/0.58  fof(f350,plain,(
% 1.59/0.58    ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) | ~spl6_17),
% 1.59/0.58    inference(resolution,[],[f220,f78])).
% 1.59/0.58  fof(f78,plain,(
% 1.59/0.58    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f44])).
% 1.59/0.58  fof(f44,plain,(
% 1.59/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f43])).
% 1.59/0.58  fof(f43,plain,(
% 1.59/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,axiom,(
% 1.59/0.58    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.59/0.58  fof(f220,plain,(
% 1.59/0.58    v7_struct_0(sK3(sK0,sK1)) | ~spl6_17),
% 1.59/0.58    inference(avatar_component_clause,[],[f218])).
% 1.59/0.58  fof(f349,plain,(
% 1.59/0.58    spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10 | spl6_18),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f348])).
% 1.59/0.58  fof(f348,plain,(
% 1.59/0.58    $false | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10 | spl6_18)),
% 1.59/0.58    inference(subsumption_resolution,[],[f347,f98])).
% 1.59/0.58  fof(f347,plain,(
% 1.59/0.58    v2_struct_0(sK0) | (spl6_1 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10 | spl6_18)),
% 1.59/0.58    inference(subsumption_resolution,[],[f346,f148])).
% 1.59/0.58  fof(f346,plain,(
% 1.59/0.58    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_3 | ~spl6_5 | ~spl6_10 | spl6_18)),
% 1.59/0.58    inference(subsumption_resolution,[],[f345,f159])).
% 1.59/0.58  fof(f345,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_3 | ~spl6_5 | spl6_18)),
% 1.59/0.58    inference(subsumption_resolution,[],[f344,f93])).
% 1.59/0.58  fof(f344,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_5 | spl6_18)),
% 1.59/0.58    inference(subsumption_resolution,[],[f343,f113])).
% 1.59/0.58  fof(f343,plain,(
% 1.59/0.58    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_18)),
% 1.59/0.58    inference(subsumption_resolution,[],[f342,f103])).
% 1.59/0.58  fof(f342,plain,(
% 1.59/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | spl6_18),
% 1.59/0.58    inference(resolution,[],[f224,f75])).
% 1.59/0.58  fof(f75,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v1_tdlat_3(sK3(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f224,plain,(
% 1.59/0.58    ~v1_tdlat_3(sK3(sK0,sK1)) | spl6_18),
% 1.59/0.58    inference(avatar_component_clause,[],[f222])).
% 1.59/0.58  fof(f222,plain,(
% 1.59/0.58    spl6_18 <=> v1_tdlat_3(sK3(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.59/0.58  fof(f333,plain,(
% 1.59/0.58    spl6_1 | ~spl6_10 | spl6_23),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f332])).
% 1.59/0.58  fof(f332,plain,(
% 1.59/0.58    $false | (spl6_1 | ~spl6_10 | spl6_23)),
% 1.59/0.58    inference(subsumption_resolution,[],[f331,f93])).
% 1.59/0.58  fof(f331,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | (~spl6_10 | spl6_23)),
% 1.59/0.58    inference(subsumption_resolution,[],[f330,f159])).
% 1.59/0.58  fof(f330,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | spl6_23),
% 1.59/0.58    inference(resolution,[],[f308,f79])).
% 1.59/0.58  fof(f79,plain,(
% 1.59/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.59/0.58  fof(f308,plain,(
% 1.59/0.58    ( ! [X0] : (~r2_hidden(sK4(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl6_23),
% 1.59/0.58    inference(resolution,[],[f306,f88])).
% 1.59/0.58  fof(f88,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f50])).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.59/0.58    inference(flattening,[],[f49])).
% 1.59/0.58  fof(f49,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.59/0.58  fof(f306,plain,(
% 1.59/0.58    ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | spl6_23),
% 1.59/0.58    inference(avatar_component_clause,[],[f304])).
% 1.59/0.58  fof(f304,plain,(
% 1.59/0.58    spl6_23 <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.59/0.58  fof(f307,plain,(
% 1.59/0.58    ~spl6_23 | spl6_8 | ~spl6_13 | ~spl6_19),
% 1.59/0.58    inference(avatar_split_clause,[],[f299,f260,f186,f146,f304])).
% 1.59/0.58  fof(f186,plain,(
% 1.59/0.58    spl6_13 <=> ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.59/0.58  fof(f260,plain,(
% 1.59/0.58    spl6_19 <=> sK1 = k1_tarski(sK4(sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.59/0.58  fof(f299,plain,(
% 1.59/0.58    ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | (spl6_8 | ~spl6_13 | ~spl6_19)),
% 1.59/0.58    inference(subsumption_resolution,[],[f296,f147])).
% 1.59/0.58  fof(f147,plain,(
% 1.59/0.58    ~v2_tex_2(sK1,sK0) | spl6_8),
% 1.59/0.58    inference(avatar_component_clause,[],[f146])).
% 1.59/0.58  fof(f296,plain,(
% 1.59/0.58    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | (~spl6_13 | ~spl6_19)),
% 1.59/0.58    inference(superposition,[],[f187,f262])).
% 1.59/0.58  fof(f262,plain,(
% 1.59/0.58    sK1 = k1_tarski(sK4(sK1)) | ~spl6_19),
% 1.59/0.58    inference(avatar_component_clause,[],[f260])).
% 1.59/0.58  fof(f187,plain,(
% 1.59/0.58    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_13),
% 1.59/0.58    inference(avatar_component_clause,[],[f186])).
% 1.59/0.58  fof(f263,plain,(
% 1.59/0.58    spl6_19 | spl6_1 | ~spl6_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f255,f150,f91,f260])).
% 1.59/0.58  fof(f255,plain,(
% 1.59/0.58    sK1 = k1_tarski(sK4(sK1)) | (spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(subsumption_resolution,[],[f253,f93])).
% 1.59/0.58  fof(f253,plain,(
% 1.59/0.58    sK1 = k1_tarski(sK4(sK1)) | v1_xboole_0(sK1) | (spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(resolution,[],[f250,f79])).
% 1.59/0.58  fof(f250,plain,(
% 1.59/0.58    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_tarski(X1) = sK1) ) | (spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(subsumption_resolution,[],[f247,f61])).
% 1.59/0.58  fof(f61,plain,(
% 1.59/0.58    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.59/0.58  fof(f247,plain,(
% 1.59/0.58    ( ! [X1] : (k1_tarski(X1) = sK1 | v1_xboole_0(k1_tarski(X1)) | ~r2_hidden(X1,sK1)) ) | (spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(resolution,[],[f242,f81])).
% 1.59/0.58  fof(f81,plain,(
% 1.59/0.58    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f45])).
% 1.59/0.58  fof(f45,plain,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f6])).
% 1.59/0.58  fof(f6,axiom,(
% 1.59/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 1.59/0.58  fof(f242,plain,(
% 1.59/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | sK1 = X2 | v1_xboole_0(X2)) ) | (spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(resolution,[],[f240,f87])).
% 1.59/0.58  fof(f87,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.58  fof(f240,plain,(
% 1.59/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = X0) ) | (spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(subsumption_resolution,[],[f239,f93])).
% 1.59/0.58  fof(f239,plain,(
% 1.59/0.58    ( ! [X0] : (v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) ) | ~spl6_9),
% 1.59/0.58    inference(resolution,[],[f152,f62])).
% 1.59/0.58  fof(f62,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.59/0.58    inference(cnf_transformation,[],[f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.59/0.58    inference(flattening,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f18])).
% 1.59/0.58  fof(f18,axiom,(
% 1.59/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.59/0.58  fof(f152,plain,(
% 1.59/0.58    v1_zfmisc_1(sK1) | ~spl6_9),
% 1.59/0.58    inference(avatar_component_clause,[],[f150])).
% 1.59/0.58  fof(f244,plain,(
% 1.59/0.58    ~spl6_8 | spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | spl6_15),
% 1.59/0.58    inference(avatar_split_clause,[],[f237,f207,f157,f111,f101,f96,f91,f146])).
% 1.59/0.58  fof(f237,plain,(
% 1.59/0.58    ~v2_tex_2(sK1,sK0) | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | spl6_15)),
% 1.59/0.58    inference(subsumption_resolution,[],[f228,f93])).
% 1.59/0.58  fof(f228,plain,(
% 1.59/0.58    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | spl6_15)),
% 1.59/0.58    inference(subsumption_resolution,[],[f227,f159])).
% 1.59/0.58  fof(f227,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | spl6_15)),
% 1.59/0.58    inference(subsumption_resolution,[],[f226,f113])).
% 1.59/0.58  fof(f226,plain,(
% 1.59/0.58    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_3 | ~spl6_5 | spl6_15)),
% 1.59/0.58    inference(resolution,[],[f215,f124])).
% 1.59/0.58  fof(f124,plain,(
% 1.59/0.58    ( ! [X1] : (m1_pre_topc(sK3(sK0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v1_xboole_0(X1)) ) | (spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.59/0.58    inference(subsumption_resolution,[],[f123,f113])).
% 1.59/0.58  fof(f123,plain,(
% 1.59/0.58    ( ! [X1] : (~l1_pre_topc(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | m1_pre_topc(sK3(sK0,X1),sK0)) ) | (spl6_2 | ~spl6_3)),
% 1.59/0.58    inference(subsumption_resolution,[],[f116,f103])).
% 1.59/0.58  fof(f116,plain,(
% 1.59/0.58    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | m1_pre_topc(sK3(sK0,X1),sK0)) ) | spl6_2),
% 1.59/0.58    inference(resolution,[],[f98,f76])).
% 1.59/0.58  fof(f76,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f215,plain,(
% 1.59/0.58    ( ! [X0] : (~m1_pre_topc(sK3(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl6_15),
% 1.59/0.58    inference(resolution,[],[f209,f69])).
% 1.59/0.58  fof(f69,plain,(
% 1.59/0.58    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f11])).
% 1.59/0.58  fof(f11,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.59/0.58  fof(f209,plain,(
% 1.59/0.58    ~l1_pre_topc(sK3(sK0,sK1)) | spl6_15),
% 1.59/0.58    inference(avatar_component_clause,[],[f207])).
% 1.59/0.58  fof(f236,plain,(
% 1.59/0.58    spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | spl6_16),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f235])).
% 1.59/0.58  fof(f235,plain,(
% 1.59/0.58    $false | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | spl6_16)),
% 1.59/0.58    inference(subsumption_resolution,[],[f234,f159])).
% 1.59/0.58  fof(f234,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | spl6_16)),
% 1.59/0.58    inference(subsumption_resolution,[],[f233,f93])).
% 1.59/0.58  fof(f233,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | spl6_16)),
% 1.59/0.58    inference(subsumption_resolution,[],[f232,f148])).
% 1.59/0.58  fof(f232,plain,(
% 1.59/0.58    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_16)),
% 1.59/0.58    inference(resolution,[],[f213,f172])).
% 1.59/0.58  fof(f172,plain,(
% 1.59/0.58    ( ! [X0] : (v2_tdlat_3(sK3(sK0,X0)) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.59/0.58    inference(resolution,[],[f124,f131])).
% 1.59/0.58  fof(f131,plain,(
% 1.59/0.58    ( ! [X4] : (~m1_pre_topc(X4,sK0) | v2_tdlat_3(X4)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.59/0.58    inference(subsumption_resolution,[],[f130,f113])).
% 1.59/0.58  fof(f130,plain,(
% 1.59/0.58    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X4,sK0) | v2_tdlat_3(X4)) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.59/0.58    inference(subsumption_resolution,[],[f129,f108])).
% 1.59/0.58  fof(f108,plain,(
% 1.59/0.58    v2_tdlat_3(sK0) | ~spl6_4),
% 1.59/0.58    inference(avatar_component_clause,[],[f106])).
% 1.59/0.58  fof(f106,plain,(
% 1.59/0.58    spl6_4 <=> v2_tdlat_3(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.59/0.58  fof(f129,plain,(
% 1.59/0.58    ( ! [X4] : (~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X4,sK0) | v2_tdlat_3(X4)) ) | (spl6_2 | ~spl6_3)),
% 1.59/0.58    inference(subsumption_resolution,[],[f119,f103])).
% 1.59/0.58  fof(f119,plain,(
% 1.59/0.58    ( ! [X4] : (~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X4,sK0) | v2_tdlat_3(X4)) ) | spl6_2),
% 1.59/0.58    inference(resolution,[],[f98,f71])).
% 1.59/0.58  fof(f71,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_tdlat_3(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f38])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f37])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f17])).
% 1.59/0.58  fof(f17,axiom,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.59/0.58  fof(f213,plain,(
% 1.59/0.58    ~v2_tdlat_3(sK3(sK0,sK1)) | spl6_16),
% 1.59/0.58    inference(avatar_component_clause,[],[f211])).
% 1.59/0.58  fof(f211,plain,(
% 1.59/0.58    spl6_16 <=> v2_tdlat_3(sK3(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.59/0.58  fof(f225,plain,(
% 1.59/0.58    spl6_17 | ~spl6_16 | ~spl6_18 | ~spl6_15 | spl6_11),
% 1.59/0.58    inference(avatar_split_clause,[],[f180,f168,f207,f222,f211,f218])).
% 1.59/0.58  fof(f168,plain,(
% 1.59/0.58    spl6_11 <=> v2_struct_0(sK3(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.59/0.58  fof(f180,plain,(
% 1.59/0.58    ~l1_pre_topc(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | ~v2_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | spl6_11),
% 1.59/0.58    inference(subsumption_resolution,[],[f178,f67])).
% 1.59/0.58  fof(f67,plain,(
% 1.59/0.58    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f32])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(flattening,[],[f31])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f15])).
% 1.59/0.58  fof(f15,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.59/0.58  fof(f178,plain,(
% 1.59/0.58    ~l1_pre_topc(sK3(sK0,sK1)) | ~v2_pre_topc(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | ~v2_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | spl6_11),
% 1.59/0.58    inference(resolution,[],[f170,f68])).
% 1.59/0.58  fof(f68,plain,(
% 1.59/0.58    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f34])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(flattening,[],[f33])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f16])).
% 1.59/0.58  fof(f16,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.59/0.58  fof(f170,plain,(
% 1.59/0.58    ~v2_struct_0(sK3(sK0,sK1)) | spl6_11),
% 1.59/0.58    inference(avatar_component_clause,[],[f168])).
% 1.59/0.58  fof(f200,plain,(
% 1.59/0.58    spl6_1 | ~spl6_10 | ~spl6_12),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f199])).
% 1.59/0.58  fof(f199,plain,(
% 1.59/0.58    $false | (spl6_1 | ~spl6_10 | ~spl6_12)),
% 1.59/0.58    inference(subsumption_resolution,[],[f196,f93])).
% 1.59/0.58  fof(f196,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | (~spl6_10 | ~spl6_12)),
% 1.59/0.58    inference(resolution,[],[f190,f159])).
% 1.59/0.58  fof(f190,plain,(
% 1.59/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1)) ) | ~spl6_12),
% 1.59/0.58    inference(resolution,[],[f184,f70])).
% 1.59/0.58  fof(f70,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f7])).
% 1.59/0.58  fof(f7,axiom,(
% 1.59/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.59/0.58  fof(f184,plain,(
% 1.59/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_12),
% 1.59/0.58    inference(avatar_component_clause,[],[f182])).
% 1.59/0.58  fof(f182,plain,(
% 1.59/0.58    spl6_12 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.59/0.58  fof(f188,plain,(
% 1.59/0.58    spl6_12 | spl6_13 | spl6_2 | ~spl6_3 | ~spl6_5),
% 1.59/0.58    inference(avatar_split_clause,[],[f162,f111,f101,f96,f186,f182])).
% 1.59/0.58  fof(f162,plain,(
% 1.59/0.58    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f161])).
% 1.59/0.58  fof(f161,plain,(
% 1.59/0.58    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.59/0.58    inference(superposition,[],[f128,f82])).
% 1.59/0.58  fof(f82,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f47])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.59/0.58    inference(flattening,[],[f46])).
% 1.59/0.58  fof(f46,plain,(
% 1.59/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f13])).
% 1.59/0.58  fof(f13,axiom,(
% 1.59/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.59/0.58  fof(f128,plain,(
% 1.59/0.58    ( ! [X3] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X3),sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.59/0.58    inference(subsumption_resolution,[],[f127,f113])).
% 1.59/0.58  fof(f127,plain,(
% 1.59/0.58    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X3),sK0)) ) | (spl6_2 | ~spl6_3)),
% 1.59/0.58    inference(subsumption_resolution,[],[f118,f103])).
% 1.59/0.58  fof(f118,plain,(
% 1.59/0.58    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X3),sK0)) ) | spl6_2),
% 1.59/0.58    inference(resolution,[],[f98,f72])).
% 1.59/0.58  fof(f72,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f20])).
% 1.59/0.58  fof(f20,axiom,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.59/0.58  fof(f171,plain,(
% 1.59/0.58    ~spl6_11 | spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10),
% 1.59/0.58    inference(avatar_split_clause,[],[f166,f157,f146,f111,f101,f96,f91,f168])).
% 1.59/0.58  fof(f166,plain,(
% 1.59/0.58    ~v2_struct_0(sK3(sK0,sK1)) | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 1.59/0.58    inference(subsumption_resolution,[],[f165,f93])).
% 1.59/0.58  fof(f165,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | ~v2_struct_0(sK3(sK0,sK1)) | (spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 1.59/0.58    inference(subsumption_resolution,[],[f163,f159])).
% 1.59/0.58  fof(f163,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_struct_0(sK3(sK0,sK1)) | (spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8)),
% 1.59/0.58    inference(resolution,[],[f122,f148])).
% 1.59/0.58  fof(f122,plain,(
% 1.59/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_struct_0(sK3(sK0,X0))) ) | (spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.59/0.58    inference(subsumption_resolution,[],[f121,f113])).
% 1.59/0.58  fof(f121,plain,(
% 1.59/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v2_struct_0(sK3(sK0,X0))) ) | (spl6_2 | ~spl6_3)),
% 1.59/0.58    inference(subsumption_resolution,[],[f115,f103])).
% 1.59/0.58  fof(f115,plain,(
% 1.59/0.58    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v2_struct_0(sK3(sK0,X0))) ) | spl6_2),
% 1.59/0.58    inference(resolution,[],[f98,f73])).
% 1.59/0.58  fof(f73,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK3(X0,X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f160,plain,(
% 1.59/0.58    spl6_10),
% 1.59/0.58    inference(avatar_split_clause,[],[f56,f157])).
% 1.59/0.58  fof(f56,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f22])).
% 1.59/0.58  fof(f22,negated_conjecture,(
% 1.59/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.59/0.58    inference(negated_conjecture,[],[f21])).
% 1.59/0.58  fof(f21,conjecture,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.59/0.58  fof(f155,plain,(
% 1.59/0.58    ~spl6_9 | ~spl6_8),
% 1.59/0.58    inference(avatar_split_clause,[],[f154,f146,f150])).
% 1.59/0.58  fof(f154,plain,(
% 1.59/0.58    ~v1_zfmisc_1(sK1) | ~spl6_8),
% 1.59/0.58    inference(subsumption_resolution,[],[f54,f148])).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f153,plain,(
% 1.59/0.58    spl6_8 | spl6_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f53,f150,f146])).
% 1.59/0.58  fof(f53,plain,(
% 1.59/0.58    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f114,plain,(
% 1.59/0.58    spl6_5),
% 1.59/0.58    inference(avatar_split_clause,[],[f60,f111])).
% 1.59/0.58  fof(f60,plain,(
% 1.59/0.58    l1_pre_topc(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f109,plain,(
% 1.59/0.58    spl6_4),
% 1.59/0.58    inference(avatar_split_clause,[],[f59,f106])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    v2_tdlat_3(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f104,plain,(
% 1.59/0.58    spl6_3),
% 1.59/0.58    inference(avatar_split_clause,[],[f58,f101])).
% 1.59/0.58  fof(f58,plain,(
% 1.59/0.58    v2_pre_topc(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f99,plain,(
% 1.59/0.58    ~spl6_2),
% 1.59/0.58    inference(avatar_split_clause,[],[f57,f96])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    ~v2_struct_0(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f94,plain,(
% 1.59/0.58    ~spl6_1),
% 1.59/0.58    inference(avatar_split_clause,[],[f55,f91])).
% 1.59/0.58  fof(f55,plain,(
% 1.59/0.58    ~v1_xboole_0(sK1)),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (20561)------------------------------
% 1.59/0.58  % (20561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (20561)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (20561)Memory used [KB]: 11001
% 1.59/0.58  % (20561)Time elapsed: 0.166 s
% 1.59/0.58  % (20561)------------------------------
% 1.59/0.58  % (20561)------------------------------
% 1.59/0.59  % (20540)Success in time 0.225 s
%------------------------------------------------------------------------------
