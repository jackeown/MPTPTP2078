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
% DateTime   : Thu Dec  3 13:22:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 238 expanded)
%              Number of leaves         :   24 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  494 (1092 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f86,f87,f108,f113,f137,f220,f253,f258,f259,f278,f280,f292,f318,f324])).

fof(f324,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_11
    | spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f321,f111,f83,f105,f74,f69])).

fof(f69,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f74,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f105,plain,
    ( spl5_11
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f83,plain,
    ( spl5_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f111,plain,
    ( spl5_12
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v2_tex_2(X0,sK0)
        | v1_zfmisc_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f321,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_8
    | ~ spl5_12 ),
    inference(resolution,[],[f85,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(X0)
        | ~ v2_tex_2(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f85,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f318,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_5
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f316,f244,f69,f105,f49,f79])).

fof(f79,plain,
    ( spl5_7
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f49,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f244,plain,
    ( spl5_29
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f316,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | ~ spl5_29 ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | ~ spl5_29 ),
    inference(superposition,[],[f37,f246])).

fof(f246,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f244])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f292,plain,
    ( spl5_10
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl5_10
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f103,f284])).

fof(f284,plain,
    ( ! [X1] : r1_xboole_0(X1,sK2(sK0,sK1))
    | ~ spl5_28 ),
    inference(resolution,[],[f242,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(sK0,sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl5_28
  <=> ! [X0] : ~ r2_hidden(X0,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f103,plain,
    ( ~ r1_xboole_0(sK1,sK2(sK0,sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_10
  <=> r1_xboole_0(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f280,plain,
    ( ~ spl5_27
    | ~ spl5_5
    | spl5_28
    | spl5_29
    | ~ spl5_30
    | spl5_6
    | ~ spl5_8
    | spl5_7
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f265,f218,f79,f83,f74,f248,f244,f241,f69,f237])).

fof(f237,plain,
    ( spl5_27
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f248,plain,
    ( spl5_30
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f218,plain,
    ( spl5_25
  <=> ! [X1,X0] :
        ( v3_tex_2(X0,sK0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(sK1,sK2(sK0,X0))
        | sK1 = sK2(sK0,X0)
        | ~ r2_hidden(X1,sK2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(sK1)
        | v1_xboole_0(sK1)
        | ~ r1_tarski(sK1,sK2(sK0,sK1))
        | sK1 = sK2(sK0,sK1)
        | ~ r2_hidden(X0,sK2(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_7
    | ~ spl5_25 ),
    inference(resolution,[],[f81,f219])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( v3_tex_2(X0,sK0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(sK1,sK2(sK0,X0))
        | sK1 = sK2(sK0,X0)
        | ~ r2_hidden(X1,sK2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f218])).

fof(f81,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f278,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_5
    | spl5_30 ),
    inference(avatar_split_clause,[],[f276,f248,f69,f105,f49,f79])).

fof(f276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | spl5_30 ),
    inference(resolution,[],[f250,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f250,plain,
    ( ~ r1_tarski(sK1,sK2(sK0,sK1))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f248])).

fof(f259,plain,
    ( ~ spl5_7
    | ~ spl5_1
    | ~ spl5_5
    | spl5_11 ),
    inference(avatar_split_clause,[],[f256,f105,f69,f49,f79])).

fof(f256,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | spl5_11 ),
    inference(resolution,[],[f107,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f258,plain,
    ( spl5_4
    | ~ spl5_8
    | ~ spl5_5
    | spl5_6
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_11 ),
    inference(avatar_split_clause,[],[f255,f105,f59,f54,f49,f74,f69,f83,f64])).

fof(f64,plain,
    ( spl5_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f54,plain,
    ( spl5_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f59,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f255,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(sK1)
    | v2_struct_0(sK0)
    | spl5_11 ),
    inference(resolution,[],[f107,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f253,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_5
    | spl5_27 ),
    inference(avatar_split_clause,[],[f252,f237,f69,f105,f49,f79])).

fof(f252,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | spl5_27 ),
    inference(resolution,[],[f239,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f239,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f237])).

fof(f220,plain,
    ( spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_25
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f216,f135,f218,f59,f54,f49,f64])).

fof(f135,plain,
    ( spl5_15
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X4,sK0)
        | ~ v2_tex_2(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK2(sK0,X4))
        | sK1 = sK2(sK0,X4)
        | ~ r1_tarski(sK1,sK2(sK0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( v3_tex_2(X0,sK0)
        | ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK2(sK0,X0))
        | sK1 = sK2(sK0,X0)
        | ~ r1_tarski(sK1,sK2(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ v1_zfmisc_1(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_15 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( v3_tex_2(X0,sK0)
        | ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK2(sK0,X0))
        | sK1 = sK2(sK0,X0)
        | ~ r1_tarski(sK1,sK2(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_zfmisc_1(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_15 ),
    inference(resolution,[],[f136,f40])).

fof(f136,plain,
    ( ! [X4,X5] :
        ( ~ v2_tex_2(X4,sK0)
        | v3_tex_2(X4,sK0)
        | ~ m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK2(sK0,X4))
        | sK1 = sK2(sK0,X4)
        | ~ r1_tarski(sK1,sK2(sK0,X4)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( ~ spl5_1
    | spl5_15
    | spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f123,f111,f74,f135,f49])).

fof(f123,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,sK2(sK0,X4))
        | sK1 = sK2(sK0,X4)
        | ~ r2_hidden(X5,sK2(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X4,sK0)
        | ~ l1_pre_topc(sK0)
        | v3_tex_2(X4,sK0) )
    | spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f120,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0
        | ~ r2_hidden(X1,X0) )
    | spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f117,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f117,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0 )
    | spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f116,f76])).

fof(f76,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | X0 = X1 )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ r1_tarski(X1,X0)
        | X0 = X1 )
    | ~ spl5_12 ),
    inference(resolution,[],[f112,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f113,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f109,f64,f59,f54,f49,f111])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(X0)
        | ~ v2_tex_2(X0,sK0) )
    | spl5_4 ),
    inference(resolution,[],[f41,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,
    ( ~ spl5_10
    | ~ spl5_5
    | ~ spl5_1
    | ~ spl5_11
    | spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f99,f79,f74,f105,f49,f69,f101])).

fof(f99,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2(sK0,sK1))
    | spl5_6
    | spl5_7 ),
    inference(resolution,[],[f97,f81])).

fof(f97,plain,
    ( ! [X0] :
        ( v3_tex_2(sK1,X0)
        | ~ v2_tex_2(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_xboole_0(sK1,sK2(X0,sK1)) )
    | spl5_6 ),
    inference(resolution,[],[f36,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_xboole_0(sK1,X0) )
    | spl5_6 ),
    inference(resolution,[],[f47,f76])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f87,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f24,f83,f79])).

fof(f24,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f86,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f25,f83,f79])).

fof(f25,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (28055)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (28047)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (28047)Refutation not found, incomplete strategy% (28047)------------------------------
% 0.21/0.47  % (28047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (28047)Memory used [KB]: 1663
% 0.21/0.47  % (28047)Time elapsed: 0.005 s
% 0.21/0.47  % (28047)------------------------------
% 0.21/0.47  % (28047)------------------------------
% 0.21/0.48  % (28055)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f86,f87,f108,f113,f137,f220,f253,f258,f259,f278,f280,f292,f318,f324])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    ~spl5_5 | spl5_6 | ~spl5_11 | spl5_8 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f321,f111,f83,f105,f74,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl5_6 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl5_11 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl5_8 <=> v1_zfmisc_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl5_12 <=> ! [X0] : (v1_xboole_0(X0) | ~v2_tex_2(X0,sK0) | v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_8 | ~spl5_12)),
% 0.21/0.48    inference(resolution,[],[f85,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    spl5_7 | ~spl5_1 | ~spl5_11 | ~spl5_5 | ~spl5_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f316,f244,f69,f105,f49,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl5_7 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl5_29 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | ~spl5_29),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f313])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | ~spl5_29),
% 0.21/0.48    inference(superposition,[],[f37,f246])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    sK1 = sK2(sK0,sK1) | ~spl5_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f244])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK2(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    spl5_10 | ~spl5_28),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f291])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    $false | (spl5_10 | ~spl5_28)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f284])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    ( ! [X1] : (r1_xboole_0(X1,sK2(sK0,sK1))) ) | ~spl5_28),
% 0.21/0.48    inference(resolution,[],[f242,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK2(sK0,sK1))) ) | ~spl5_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    spl5_28 <=> ! [X0] : ~r2_hidden(X0,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~r1_xboole_0(sK1,sK2(sK0,sK1)) | spl5_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl5_10 <=> r1_xboole_0(sK1,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    ~spl5_27 | ~spl5_5 | spl5_28 | spl5_29 | ~spl5_30 | spl5_6 | ~spl5_8 | spl5_7 | ~spl5_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f265,f218,f79,f83,f74,f248,f244,f241,f69,f237])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl5_27 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    spl5_30 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl5_25 <=> ! [X1,X0] : (v3_tex_2(X0,sK0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~r1_tarski(sK1,sK2(sK0,X0)) | sK1 = sK2(sK0,X0) | ~r2_hidden(X1,sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~r1_tarski(sK1,sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1) | ~r2_hidden(X0,sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_7 | ~spl5_25)),
% 0.21/0.48    inference(resolution,[],[f81,f219])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_tex_2(X0,sK0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~r1_tarski(sK1,sK2(sK0,X0)) | sK1 = sK2(sK0,X0) | ~r2_hidden(X1,sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~v3_tex_2(sK1,sK0) | spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    spl5_7 | ~spl5_1 | ~spl5_11 | ~spl5_5 | spl5_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f276,f248,f69,f105,f49,f79])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | spl5_30),
% 0.21/0.48    inference(resolution,[],[f250,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2(sK0,sK1)) | spl5_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f248])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ~spl5_7 | ~spl5_1 | ~spl5_5 | spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f256,f105,f69,f49,f79])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tex_2(sK1,sK0) | spl5_11),
% 0.21/0.48    inference(resolution,[],[f107,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | spl5_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl5_4 | ~spl5_8 | ~spl5_5 | spl5_6 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f255,f105,f59,f54,f49,f74,f69,f83,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl5_4 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl5_2 <=> v2_tdlat_3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl5_3 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(sK1) | v2_struct_0(sK0) | spl5_11),
% 0.21/0.48    inference(resolution,[],[f107,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    spl5_7 | ~spl5_1 | ~spl5_11 | ~spl5_5 | spl5_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f252,f237,f69,f105,f49,f79])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | spl5_27),
% 0.21/0.48    inference(resolution,[],[f239,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f237])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    spl5_4 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_25 | ~spl5_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f216,f135,f218,f59,f54,f49,f64])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl5_15 <=> ! [X5,X4] : (~m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X4,sK0) | ~v2_tex_2(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK2(sK0,X4)) | sK1 = sK2(sK0,X4) | ~r1_tarski(sK1,sK2(sK0,X4)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_tex_2(X0,sK0) | ~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2(sK0,X0)) | sK1 = sK2(sK0,X0) | ~r1_tarski(sK1,sK2(sK0,X0)) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v2_struct_0(sK0)) ) | ~spl5_15),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_tex_2(X0,sK0) | ~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2(sK0,X0)) | sK1 = sK2(sK0,X0) | ~r1_tarski(sK1,sK2(sK0,X0)) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_struct_0(sK0)) ) | ~spl5_15),
% 0.21/0.48    inference(resolution,[],[f136,f40])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~v2_tex_2(X4,sK0) | v3_tex_2(X4,sK0) | ~m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK2(sK0,X4)) | sK1 = sK2(sK0,X4) | ~r1_tarski(sK1,sK2(sK0,X4))) ) | ~spl5_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~spl5_1 | spl5_15 | spl5_6 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f111,f74,f135,f49])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,sK2(sK0,X4)) | sK1 = sK2(sK0,X4) | ~r2_hidden(X5,sK2(sK0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X4,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(X4,sK0)) ) | (spl5_6 | ~spl5_12)),
% 0.21/0.48    inference(resolution,[],[f120,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0 | ~r2_hidden(X1,X0)) ) | (spl5_6 | ~spl5_12)),
% 0.21/0.48    inference(resolution,[],[f117,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0) | sK1 = X0) ) | (spl5_6 | ~spl5_12)),
% 0.21/0.48    inference(resolution,[],[f116,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | X0 = X1) ) | ~spl5_12),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~r1_tarski(X1,X0) | X0 = X1) ) | ~spl5_12),
% 0.21/0.48    inference(resolution,[],[f112,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl5_12 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f109,f64,f59,f54,f49,f111])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) ) | spl5_4),
% 0.21/0.48    inference(resolution,[],[f41,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~spl5_10 | ~spl5_5 | ~spl5_1 | ~spl5_11 | spl5_6 | spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f99,f79,f74,f105,f49,f69,f101])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2(sK0,sK1)) | (spl5_6 | spl5_7)),
% 0.21/0.48    inference(resolution,[],[f97,f81])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (v3_tex_2(sK1,X0) | ~v2_tex_2(sK1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_xboole_0(sK1,sK2(X0,sK1))) ) | spl5_6),
% 0.21/0.48    inference(resolution,[],[f36,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_xboole_0(sK1,X0)) ) | spl5_6),
% 0.21/0.48    inference(resolution,[],[f47,f76])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl5_7 | spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f83,f79])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~spl5_7 | ~spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f83,f79])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f74])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f69])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f54])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v2_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f49])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (28055)------------------------------
% 0.21/0.48  % (28055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28055)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (28055)Memory used [KB]: 6396
% 0.21/0.48  % (28055)Time elapsed: 0.017 s
% 0.21/0.48  % (28055)------------------------------
% 0.21/0.48  % (28055)------------------------------
% 0.21/0.48  % (28039)Success in time 0.12 s
%------------------------------------------------------------------------------
