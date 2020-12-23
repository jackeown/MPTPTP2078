%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:35 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 335 expanded)
%              Number of leaves         :   34 ( 152 expanded)
%              Depth                    :    9
%              Number of atoms          :  667 (1741 expanded)
%              Number of equality atoms :   18 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f85,f89,f93,f97,f101,f105,f109,f119,f140,f154,f164,f165,f170,f186,f190,f195,f201,f203,f206,f211,f217,f220,f221])).

fof(f221,plain,
    ( ~ spl3_18
    | spl3_2
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f172,f149,f117,f80,f152])).

fof(f152,plain,
    ( spl3_18
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f80,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f117,plain,
    ( spl3_9
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f149,plain,
    ( spl3_17
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f172,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f171,f118])).

fof(f118,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f171,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl3_17 ),
    inference(resolution,[],[f150,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f150,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f220,plain,
    ( ~ spl3_5
    | ~ spl3_22
    | spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f218,f209,f107,f199,f95])).

fof(f95,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f199,plain,
    ( spl3_22
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f107,plain,
    ( spl3_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f209,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f218,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_8
    | ~ spl3_23 ),
    inference(resolution,[],[f210,f108])).

fof(f108,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f210,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f209])).

fof(f217,plain,
    ( ~ spl3_22
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_8
    | spl3_20 ),
    inference(avatar_split_clause,[],[f214,f176,f107,f95,f99,f103,f199])).

fof(f103,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( spl3_6
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f176,plain,
    ( spl3_20
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_8
    | spl3_20 ),
    inference(resolution,[],[f212,f108])).

fof(f212,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0) )
    | spl3_20 ),
    inference(resolution,[],[f177,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f177,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f211,plain,
    ( spl3_23
    | spl3_10
    | spl3_17
    | ~ spl3_20
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f207,f135,f176,f149,f125,f209])).

fof(f125,plain,
    ( spl3_10
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f135,plain,
    ( spl3_13
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ v2_tdlat_3(sK2(sK0,sK1))
        | v7_struct_0(sK2(sK0,sK1))
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_13 ),
    inference(resolution,[],[f191,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ v2_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_tdlat_3(X1)
              & ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).

fof(f191,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f206,plain,
    ( ~ spl3_3
    | ~ spl3_22
    | ~ spl3_5
    | spl3_8
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f205,f193,f77,f107,f95,f199,f87])).

fof(f87,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f193,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(resolution,[],[f194,f83])).

fof(f83,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f203,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_4
    | ~ spl3_3
    | spl3_22 ),
    inference(avatar_split_clause,[],[f202,f199,f87,f91,f95,f107])).

fof(f91,plain,
    ( spl3_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_22 ),
    inference(resolution,[],[f200,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f200,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( ~ spl3_3
    | ~ spl3_22
    | ~ spl3_5
    | spl3_8
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f197,f138,f77,f107,f95,f199,f87])).

fof(f138,plain,
    ( spl3_14
  <=> ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_tex_2(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f197,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_14 ),
    inference(resolution,[],[f139,f78])).

fof(f78,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f139,plain,
    ( ! [X1] :
        ( v2_tex_2(sK1,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f195,plain,
    ( spl3_10
    | spl3_13
    | spl3_21
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f188,f117,f193,f135,f125])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9 ),
    inference(superposition,[],[f75,f118])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f190,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_4
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f189,f125,f87,f91,f95,f107])).

fof(f189,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f126,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f126,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f186,plain,
    ( spl3_8
    | spl3_4
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_5
    | spl3_19 ),
    inference(avatar_split_clause,[],[f184,f168,f95,f103,f87,f91,f107])).

fof(f168,plain,
    ( spl3_19
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f184,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | spl3_19 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_19 ),
    inference(resolution,[],[f173,f67])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl3_19 ),
    inference(resolution,[],[f169,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f169,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( ~ spl3_11
    | spl3_10
    | ~ spl3_17
    | ~ spl3_19
    | spl3_13 ),
    inference(avatar_split_clause,[],[f156,f135,f168,f149,f125,f128])).

fof(f128,plain,
    ( spl3_11
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f156,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_13 ),
    inference(resolution,[],[f136,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).

fof(f136,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f165,plain,
    ( ~ spl3_11
    | spl3_18 ),
    inference(avatar_split_clause,[],[f157,f152,f128])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_18 ),
    inference(resolution,[],[f153,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f153,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f164,plain,
    ( spl3_8
    | spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11 ),
    inference(avatar_split_clause,[],[f161,f128,f95,f87,f91,f107])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(resolution,[],[f155,f67])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl3_11 ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f129,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f154,plain,
    ( spl3_17
    | ~ spl3_18
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f123,f117,f80,f152,f149])).

fof(f123,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_9 ),
    inference(superposition,[],[f63,f118])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f140,plain,
    ( spl3_10
    | ~ spl3_13
    | spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f121,f117,f138,f135,f125])).

fof(f121,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v1_tdlat_3(sK2(sK0,sK1))
        | v2_tex_2(sK1,X1)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl3_9 ),
    inference(superposition,[],[f74,f118])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_9
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f113,f91,f87,f117,f95,f107])).

fof(f113,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f112,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl3_4 ),
    inference(resolution,[],[f68,f92])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f47,f107])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f105,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f103])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f51,f91])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f87])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f53,f80,f77])).

fof(f53,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f80,f77])).

fof(f54,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n020.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 16:13:52 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.44  % (9530)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.17/0.44  % (9530)Refutation found. Thanks to Tanya!
% 0.17/0.44  % SZS status Theorem for theBenchmark
% 0.17/0.45  % (9538)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.17/0.45  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f222,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(avatar_sat_refutation,[],[f82,f85,f89,f93,f97,f101,f105,f109,f119,f140,f154,f164,f165,f170,f186,f190,f195,f201,f203,f206,f211,f217,f220,f221])).
% 0.17/0.45  fof(f221,plain,(
% 0.17/0.45    ~spl3_18 | spl3_2 | ~spl3_9 | ~spl3_17),
% 0.17/0.45    inference(avatar_split_clause,[],[f172,f149,f117,f80,f152])).
% 0.17/0.45  fof(f152,plain,(
% 0.17/0.45    spl3_18 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.17/0.45  fof(f80,plain,(
% 0.17/0.45    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.45  fof(f117,plain,(
% 0.17/0.45    spl3_9 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.17/0.45  fof(f149,plain,(
% 0.17/0.45    spl3_17 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.17/0.45  fof(f172,plain,(
% 0.17/0.45    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | (~spl3_9 | ~spl3_17)),
% 0.17/0.45    inference(forward_demodulation,[],[f171,f118])).
% 0.17/0.45  fof(f118,plain,(
% 0.17/0.45    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl3_9),
% 0.17/0.45    inference(avatar_component_clause,[],[f117])).
% 0.17/0.45  fof(f171,plain,(
% 0.17/0.45    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl3_17),
% 0.17/0.45    inference(resolution,[],[f150,f72])).
% 0.17/0.45  fof(f72,plain,(
% 0.17/0.45    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f36,plain,(
% 0.17/0.45    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f35])).
% 0.17/0.45  fof(f35,plain,(
% 0.17/0.45    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f5])).
% 0.17/0.45  fof(f5,axiom,(
% 0.17/0.45    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.17/0.45  fof(f150,plain,(
% 0.17/0.45    v7_struct_0(sK2(sK0,sK1)) | ~spl3_17),
% 0.17/0.45    inference(avatar_component_clause,[],[f149])).
% 0.17/0.45  fof(f220,plain,(
% 0.17/0.45    ~spl3_5 | ~spl3_22 | spl3_8 | ~spl3_23),
% 0.17/0.45    inference(avatar_split_clause,[],[f218,f209,f107,f199,f95])).
% 0.17/0.45  fof(f95,plain,(
% 0.17/0.45    spl3_5 <=> l1_pre_topc(sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.17/0.45  fof(f199,plain,(
% 0.17/0.45    spl3_22 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.17/0.45  fof(f107,plain,(
% 0.17/0.45    spl3_8 <=> v2_struct_0(sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.17/0.45  fof(f209,plain,(
% 0.17/0.45    spl3_23 <=> ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.17/0.45  fof(f218,plain,(
% 0.17/0.45    ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (spl3_8 | ~spl3_23)),
% 0.17/0.45    inference(resolution,[],[f210,f108])).
% 0.17/0.45  fof(f108,plain,(
% 0.17/0.45    ~v2_struct_0(sK0) | spl3_8),
% 0.17/0.45    inference(avatar_component_clause,[],[f107])).
% 0.17/0.45  fof(f210,plain,(
% 0.17/0.45    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_23),
% 0.17/0.45    inference(avatar_component_clause,[],[f209])).
% 0.17/0.45  fof(f217,plain,(
% 0.17/0.45    ~spl3_22 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_8 | spl3_20),
% 0.17/0.45    inference(avatar_split_clause,[],[f214,f176,f107,f95,f99,f103,f199])).
% 0.17/0.45  fof(f103,plain,(
% 0.17/0.45    spl3_7 <=> v2_pre_topc(sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.17/0.45  fof(f99,plain,(
% 0.17/0.45    spl3_6 <=> v2_tdlat_3(sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.17/0.45  fof(f176,plain,(
% 0.17/0.45    spl3_20 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.17/0.45  fof(f214,plain,(
% 0.17/0.45    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | (spl3_8 | spl3_20)),
% 0.17/0.45    inference(resolution,[],[f212,f108])).
% 0.17/0.45  fof(f212,plain,(
% 0.17/0.45    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0)) ) | spl3_20),
% 0.17/0.45    inference(resolution,[],[f177,f71])).
% 0.17/0.45  fof(f71,plain,(
% 0.17/0.45    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f34])).
% 0.17/0.45  fof(f34,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f33])).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f10])).
% 0.17/0.45  fof(f10,axiom,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.17/0.45  fof(f177,plain,(
% 0.17/0.45    ~v2_tdlat_3(sK2(sK0,sK1)) | spl3_20),
% 0.17/0.45    inference(avatar_component_clause,[],[f176])).
% 0.17/0.45  fof(f211,plain,(
% 0.17/0.45    spl3_23 | spl3_10 | spl3_17 | ~spl3_20 | ~spl3_13),
% 0.17/0.45    inference(avatar_split_clause,[],[f207,f135,f176,f149,f125,f209])).
% 0.17/0.45  fof(f125,plain,(
% 0.17/0.45    spl3_10 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.17/0.45  fof(f135,plain,(
% 0.17/0.45    spl3_13 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.17/0.45  fof(f207,plain,(
% 0.17/0.45    ( ! [X0] : (~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_13),
% 0.17/0.45    inference(resolution,[],[f191,f65])).
% 0.17/0.45  fof(f65,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f28])).
% 0.17/0.45  fof(f28,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f27])).
% 0.17/0.45  fof(f27,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f8])).
% 0.17/0.45  fof(f8,axiom,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_tdlat_3(X1) & ~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).
% 0.17/0.45  fof(f191,plain,(
% 0.17/0.45    v1_tdlat_3(sK2(sK0,sK1)) | ~spl3_13),
% 0.17/0.45    inference(avatar_component_clause,[],[f135])).
% 0.17/0.45  fof(f206,plain,(
% 0.17/0.45    ~spl3_3 | ~spl3_22 | ~spl3_5 | spl3_8 | ~spl3_1 | ~spl3_21),
% 0.17/0.45    inference(avatar_split_clause,[],[f205,f193,f77,f107,f95,f199,f87])).
% 0.17/0.45  fof(f87,plain,(
% 0.17/0.45    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.45  fof(f77,plain,(
% 0.17/0.45    spl3_1 <=> v2_tex_2(sK1,sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.45  fof(f193,plain,(
% 0.17/0.45    spl3_21 <=> ! [X0] : (~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.17/0.45  fof(f205,plain,(
% 0.17/0.45    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_21)),
% 0.17/0.45    inference(resolution,[],[f194,f83])).
% 0.17/0.45  fof(f83,plain,(
% 0.17/0.45    v2_tex_2(sK1,sK0) | ~spl3_1),
% 0.17/0.45    inference(avatar_component_clause,[],[f77])).
% 0.17/0.45  fof(f194,plain,(
% 0.17/0.45    ( ! [X0] : (~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_21),
% 0.17/0.45    inference(avatar_component_clause,[],[f193])).
% 0.17/0.45  fof(f203,plain,(
% 0.17/0.45    spl3_8 | ~spl3_5 | spl3_4 | ~spl3_3 | spl3_22),
% 0.17/0.45    inference(avatar_split_clause,[],[f202,f199,f87,f91,f95,f107])).
% 0.17/0.45  fof(f91,plain,(
% 0.17/0.45    spl3_4 <=> v1_xboole_0(sK1)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.17/0.45  fof(f202,plain,(
% 0.17/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_22),
% 0.17/0.45    inference(resolution,[],[f200,f67])).
% 0.17/0.45  fof(f67,plain,(
% 0.17/0.45    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f45])).
% 0.17/0.45  fof(f45,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f44])).
% 0.17/0.45  fof(f44,plain,(
% 0.17/0.45    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f30,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f29])).
% 0.17/0.45  fof(f29,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f15])).
% 0.17/0.45  fof(f15,plain,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.17/0.45    inference(pure_predicate_removal,[],[f11])).
% 0.17/0.45  fof(f11,axiom,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.17/0.45  fof(f200,plain,(
% 0.17/0.45    ~m1_pre_topc(sK2(sK0,sK1),sK0) | spl3_22),
% 0.17/0.45    inference(avatar_component_clause,[],[f199])).
% 0.17/0.45  fof(f201,plain,(
% 0.17/0.45    ~spl3_3 | ~spl3_22 | ~spl3_5 | spl3_8 | spl3_1 | ~spl3_14),
% 0.17/0.45    inference(avatar_split_clause,[],[f197,f138,f77,f107,f95,f199,f87])).
% 0.17/0.45  fof(f138,plain,(
% 0.17/0.45    spl3_14 <=> ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2(sK0,sK1),X1) | v2_tex_2(sK1,X1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.17/0.45  fof(f197,plain,(
% 0.17/0.45    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_14)),
% 0.17/0.45    inference(resolution,[],[f139,f78])).
% 0.17/0.45  fof(f78,plain,(
% 0.17/0.45    ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.17/0.45    inference(avatar_component_clause,[],[f77])).
% 0.17/0.45  fof(f139,plain,(
% 0.17/0.45    ( ! [X1] : (v2_tex_2(sK1,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))) ) | ~spl3_14),
% 0.17/0.45    inference(avatar_component_clause,[],[f138])).
% 0.17/0.45  fof(f195,plain,(
% 0.17/0.45    spl3_10 | spl3_13 | spl3_21 | ~spl3_9),
% 0.17/0.45    inference(avatar_split_clause,[],[f188,f117,f193,f135,f125])).
% 0.17/0.45  fof(f188,plain,(
% 0.17/0.45    ( ! [X0] : (~v2_tex_2(sK1,X0) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_9),
% 0.17/0.45    inference(superposition,[],[f75,f118])).
% 0.17/0.45  fof(f75,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~v2_tex_2(u1_struct_0(X1),X0) | v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(equality_resolution,[],[f69])).
% 0.17/0.45  fof(f69,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f46])).
% 0.17/0.45  fof(f46,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(nnf_transformation,[],[f32])).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f12])).
% 0.17/0.45  fof(f12,axiom,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.17/0.45  fof(f190,plain,(
% 0.17/0.45    spl3_8 | ~spl3_5 | spl3_4 | ~spl3_3 | ~spl3_10),
% 0.17/0.45    inference(avatar_split_clause,[],[f189,f125,f87,f91,f95,f107])).
% 0.17/0.45  fof(f189,plain,(
% 0.17/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.17/0.45    inference(resolution,[],[f126,f66])).
% 0.17/0.45  fof(f66,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f45])).
% 0.17/0.45  fof(f126,plain,(
% 0.17/0.45    v2_struct_0(sK2(sK0,sK1)) | ~spl3_10),
% 0.17/0.45    inference(avatar_component_clause,[],[f125])).
% 0.17/0.45  fof(f186,plain,(
% 0.17/0.45    spl3_8 | spl3_4 | ~spl3_3 | ~spl3_7 | ~spl3_5 | spl3_19),
% 0.17/0.45    inference(avatar_split_clause,[],[f184,f168,f95,f103,f87,f91,f107])).
% 0.17/0.45  fof(f168,plain,(
% 0.17/0.45    spl3_19 <=> v2_pre_topc(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.17/0.45  fof(f184,plain,(
% 0.17/0.45    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v2_struct_0(sK0) | spl3_19),
% 0.17/0.45    inference(duplicate_literal_removal,[],[f181])).
% 0.17/0.45  fof(f181,plain,(
% 0.17/0.45    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_19),
% 0.17/0.45    inference(resolution,[],[f173,f67])).
% 0.17/0.45  fof(f173,plain,(
% 0.17/0.45    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl3_19),
% 0.17/0.45    inference(resolution,[],[f169,f73])).
% 0.17/0.45  fof(f73,plain,(
% 0.17/0.45    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f38])).
% 0.17/0.45  fof(f38,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.17/0.45    inference(flattening,[],[f37])).
% 0.17/0.45  fof(f37,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f1])).
% 0.17/0.45  fof(f1,axiom,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.17/0.45  fof(f169,plain,(
% 0.17/0.45    ~v2_pre_topc(sK2(sK0,sK1)) | spl3_19),
% 0.17/0.45    inference(avatar_component_clause,[],[f168])).
% 0.17/0.45  fof(f170,plain,(
% 0.17/0.45    ~spl3_11 | spl3_10 | ~spl3_17 | ~spl3_19 | spl3_13),
% 0.17/0.45    inference(avatar_split_clause,[],[f156,f135,f168,f149,f125,f128])).
% 0.17/0.45  fof(f128,plain,(
% 0.17/0.45    spl3_11 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.17/0.45  fof(f156,plain,(
% 0.17/0.45    ~v2_pre_topc(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | spl3_13),
% 0.17/0.45    inference(resolution,[],[f136,f60])).
% 0.17/0.45  fof(f60,plain,(
% 0.17/0.45    ( ! [X0] : (v1_tdlat_3(X0) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f23])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    ! [X0] : ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.17/0.45    inference(flattening,[],[f22])).
% 0.17/0.45  fof(f22,plain,(
% 0.17/0.45    ! [X0] : (((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f7])).
% 0.17/0.45  fof(f7,axiom,(
% 0.17/0.45    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => (v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).
% 0.17/0.45  fof(f136,plain,(
% 0.17/0.45    ~v1_tdlat_3(sK2(sK0,sK1)) | spl3_13),
% 0.17/0.45    inference(avatar_component_clause,[],[f135])).
% 0.17/0.45  fof(f165,plain,(
% 0.17/0.45    ~spl3_11 | spl3_18),
% 0.17/0.45    inference(avatar_split_clause,[],[f157,f152,f128])).
% 0.17/0.45  fof(f157,plain,(
% 0.17/0.45    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_18),
% 0.17/0.45    inference(resolution,[],[f153,f55])).
% 0.17/0.45  fof(f55,plain,(
% 0.17/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f18])).
% 0.17/0.45  fof(f18,plain,(
% 0.17/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f2])).
% 0.17/0.45  fof(f2,axiom,(
% 0.17/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.17/0.45  fof(f153,plain,(
% 0.17/0.45    ~l1_struct_0(sK2(sK0,sK1)) | spl3_18),
% 0.17/0.45    inference(avatar_component_clause,[],[f152])).
% 0.17/0.45  fof(f164,plain,(
% 0.17/0.45    spl3_8 | spl3_4 | ~spl3_3 | ~spl3_5 | spl3_11),
% 0.17/0.45    inference(avatar_split_clause,[],[f161,f128,f95,f87,f91,f107])).
% 0.17/0.45  fof(f161,plain,(
% 0.17/0.45    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v2_struct_0(sK0) | spl3_11),
% 0.17/0.45    inference(duplicate_literal_removal,[],[f158])).
% 0.17/0.45  fof(f158,plain,(
% 0.17/0.45    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_11),
% 0.17/0.45    inference(resolution,[],[f155,f67])).
% 0.17/0.45  fof(f155,plain,(
% 0.17/0.45    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl3_11),
% 0.17/0.45    inference(resolution,[],[f129,f62])).
% 0.17/0.45  fof(f62,plain,(
% 0.17/0.45    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f24])).
% 0.17/0.45  fof(f24,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f3])).
% 0.17/0.45  fof(f3,axiom,(
% 0.17/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.17/0.45  fof(f129,plain,(
% 0.17/0.45    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_11),
% 0.17/0.45    inference(avatar_component_clause,[],[f128])).
% 0.17/0.45  fof(f154,plain,(
% 0.17/0.45    spl3_17 | ~spl3_18 | ~spl3_2 | ~spl3_9),
% 0.17/0.45    inference(avatar_split_clause,[],[f123,f117,f80,f152,f149])).
% 0.17/0.45  fof(f123,plain,(
% 0.17/0.45    ~v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~spl3_9),
% 0.17/0.45    inference(superposition,[],[f63,f118])).
% 0.17/0.45  fof(f63,plain,(
% 0.17/0.45    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f26])).
% 0.17/0.45  fof(f26,plain,(
% 0.17/0.45    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f25])).
% 0.17/0.45  fof(f25,plain,(
% 0.17/0.45    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f4])).
% 0.17/0.45  fof(f4,axiom,(
% 0.17/0.45    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.17/0.45  fof(f140,plain,(
% 0.17/0.45    spl3_10 | ~spl3_13 | spl3_14 | ~spl3_9),
% 0.17/0.45    inference(avatar_split_clause,[],[f121,f117,f138,f135,f125])).
% 0.17/0.45  fof(f121,plain,(
% 0.17/0.45    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,X1) | ~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl3_9),
% 0.17/0.45    inference(superposition,[],[f74,f118])).
% 0.17/0.45  fof(f74,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(equality_resolution,[],[f70])).
% 0.17/0.45  fof(f70,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f46])).
% 0.17/0.45  fof(f119,plain,(
% 0.17/0.45    spl3_8 | ~spl3_5 | spl3_9 | ~spl3_3 | spl3_4),
% 0.17/0.45    inference(avatar_split_clause,[],[f113,f91,f87,f117,f95,f107])).
% 0.17/0.45  fof(f113,plain,(
% 0.17/0.45    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | spl3_4)),
% 0.17/0.45    inference(resolution,[],[f112,f88])).
% 0.17/0.45  fof(f88,plain,(
% 0.17/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.17/0.45    inference(avatar_component_clause,[],[f87])).
% 0.17/0.45  fof(f112,plain,(
% 0.17/0.45    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl3_4),
% 0.17/0.45    inference(resolution,[],[f68,f92])).
% 0.17/0.45  fof(f92,plain,(
% 0.17/0.45    ~v1_xboole_0(sK1) | spl3_4),
% 0.17/0.45    inference(avatar_component_clause,[],[f91])).
% 0.17/0.45  fof(f68,plain,(
% 0.17/0.45    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f45])).
% 0.17/0.45  fof(f109,plain,(
% 0.17/0.45    ~spl3_8),
% 0.17/0.45    inference(avatar_split_clause,[],[f47,f107])).
% 0.17/0.45  fof(f47,plain,(
% 0.17/0.45    ~v2_struct_0(sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f43,plain,(
% 0.17/0.45    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 0.17/0.45  fof(f41,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f42,plain,(
% 0.17/0.45    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f40,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f39])).
% 0.17/0.45  fof(f39,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.17/0.45    inference(nnf_transformation,[],[f17])).
% 0.17/0.45  fof(f17,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f16])).
% 0.17/0.45  fof(f16,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f14])).
% 0.17/0.45  fof(f14,negated_conjecture,(
% 0.17/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.17/0.45    inference(negated_conjecture,[],[f13])).
% 0.17/0.45  fof(f13,conjecture,(
% 0.17/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.17/0.45  fof(f105,plain,(
% 0.17/0.45    spl3_7),
% 0.17/0.45    inference(avatar_split_clause,[],[f48,f103])).
% 0.17/0.45  fof(f48,plain,(
% 0.17/0.45    v2_pre_topc(sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f101,plain,(
% 0.17/0.45    spl3_6),
% 0.17/0.45    inference(avatar_split_clause,[],[f49,f99])).
% 0.17/0.45  fof(f49,plain,(
% 0.17/0.45    v2_tdlat_3(sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f97,plain,(
% 0.17/0.45    spl3_5),
% 0.17/0.45    inference(avatar_split_clause,[],[f50,f95])).
% 0.17/0.45  fof(f50,plain,(
% 0.17/0.45    l1_pre_topc(sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f93,plain,(
% 0.17/0.45    ~spl3_4),
% 0.17/0.45    inference(avatar_split_clause,[],[f51,f91])).
% 0.17/0.45  fof(f51,plain,(
% 0.17/0.45    ~v1_xboole_0(sK1)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f89,plain,(
% 0.17/0.45    spl3_3),
% 0.17/0.45    inference(avatar_split_clause,[],[f52,f87])).
% 0.17/0.45  fof(f52,plain,(
% 0.17/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f85,plain,(
% 0.17/0.45    spl3_1 | spl3_2),
% 0.17/0.45    inference(avatar_split_clause,[],[f53,f80,f77])).
% 0.17/0.45  fof(f53,plain,(
% 0.17/0.45    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  fof(f82,plain,(
% 0.17/0.45    ~spl3_1 | ~spl3_2),
% 0.17/0.45    inference(avatar_split_clause,[],[f54,f80,f77])).
% 0.17/0.45  fof(f54,plain,(
% 0.17/0.45    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f43])).
% 0.17/0.45  % SZS output end Proof for theBenchmark
% 0.17/0.45  % (9530)------------------------------
% 0.17/0.45  % (9530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (9530)Termination reason: Refutation
% 0.17/0.45  
% 0.17/0.45  % (9530)Memory used [KB]: 10746
% 0.17/0.45  % (9530)Time elapsed: 0.058 s
% 0.17/0.45  % (9530)------------------------------
% 0.17/0.45  % (9530)------------------------------
% 0.17/0.46  % (9523)Success in time 0.13 s
%------------------------------------------------------------------------------
