%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 284 expanded)
%              Number of leaves         :   38 ( 131 expanded)
%              Depth                    :    9
%              Number of atoms          :  686 (1652 expanded)
%              Number of equality atoms :   38 ( 130 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f475,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f96,f100,f104,f108,f112,f116,f124,f250,f280,f321,f359,f361,f370,f385,f407,f421,f453,f459,f471,f474])).

fof(f474,plain,
    ( ~ spl3_37
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl3_37
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f406,f366])).

fof(f366,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl3_37
  <=> ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f406,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK1))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl3_45
  <=> m1_subset_1(k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f471,plain,
    ( ~ spl3_38
    | spl3_1
    | ~ spl3_25
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f461,f457,f275,f78,f368])).

fof(f368,plain,
    ( spl3_38
  <=> m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f78,plain,
    ( spl3_1
  <=> k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f275,plain,
    ( spl3_25
  <=> r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f457,plain,
    ( spl3_51
  <=> ! [X0] :
        ( k11_yellow_6(sK0,sK1) = X0
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f461,plain,
    ( k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_25
    | ~ spl3_51 ),
    inference(resolution,[],[f458,f276])).

fof(f276,plain,
    ( r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f275])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | k11_yellow_6(sK0,sK1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f457])).

fof(f459,plain,
    ( spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_2
    | spl3_51
    | ~ spl3_3
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f454,f451,f86,f457,f82,f90,f94,f98])).

fof(f98,plain,
    ( spl3_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( spl3_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( spl3_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f82,plain,
    ( spl3_2
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( spl3_3
  <=> v1_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f451,plain,
    ( spl3_50
  <=> ! [X1,X0] :
        ( k11_yellow_6(sK0,X0) = X1
        | ~ v1_yellow_6(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f454,plain,
    ( ! [X0] :
        ( k11_yellow_6(sK0,sK1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl3_3
    | ~ spl3_50 ),
    inference(resolution,[],[f452,f87])).

fof(f87,plain,
    ( v1_yellow_6(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( ~ v1_yellow_6(X0,sK0)
        | k11_yellow_6(sK0,X0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f451])).

fof(f453,plain,
    ( spl3_10
    | ~ spl3_9
    | ~ spl3_7
    | spl3_50
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f449,f419,f451,f102,f110,f114])).

fof(f114,plain,
    ( spl3_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f110,plain,
    ( spl3_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f102,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f419,plain,
    ( spl3_47
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,X1))
        | k11_yellow_6(sK0,X1) = X0
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,sK0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f449,plain,
    ( ! [X0,X1] :
        ( k11_yellow_6(sK0,X0) = X1
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_yellow_6(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_47 ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,
    ( ! [X0,X1] :
        ( k11_yellow_6(sK0,X0) = X1
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_47 ),
    inference(resolution,[],[f420,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( ( v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(f420,plain,
    ( ! [X0,X1] :
        ( ~ v3_yellow_6(X1,sK0)
        | k11_yellow_6(sK0,X1) = X0
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,X1))
        | ~ l1_waybel_0(X1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f419])).

fof(f421,plain,
    ( spl3_10
    | ~ spl3_9
    | ~ spl3_7
    | spl3_47
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f417,f106,f419,f102,f110,f114])).

fof(f106,plain,
    ( spl3_8
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(X1,sK0)
        | ~ v3_yellow_6(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | k11_yellow_6(sK0,X1) = X0
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f59,f107])).

fof(f107,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k11_yellow_6(X0,X1) = X2
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k11_yellow_6(X0,X1) = X2
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | k11_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

fof(f407,plain,
    ( spl3_45
    | ~ spl3_11
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f400,f383,f122,f405])).

fof(f122,plain,
    ( spl3_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f383,plain,
    ( spl3_41
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f400,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK1))
    | ~ spl3_11
    | ~ spl3_41 ),
    inference(resolution,[],[f384,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl3_11 ),
    inference(resolution,[],[f123,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f123,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f384,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f383])).

fof(f385,plain,
    ( spl3_41
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f373,f365,f383])).

fof(f373,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_37 ),
    inference(resolution,[],[f366,f144])).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f68,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f370,plain,
    ( spl3_10
    | ~ spl3_36
    | spl3_6
    | ~ spl3_2
    | spl3_37
    | spl3_38
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f363,f354,f368,f365,f82,f98,f357,f114])).

fof(f357,plain,
    ( spl3_36
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f354,plain,
    ( spl3_35
  <=> ! [X0] :
        ( k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f363,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_35 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl3_35 ),
    inference(superposition,[],[f74,f355])).

fof(f355,plain,
    ( ! [X0] :
        ( k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f354])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(f361,plain,
    ( ~ spl3_7
    | spl3_36 ),
    inference(avatar_split_clause,[],[f360,f357,f102])).

fof(f360,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_36 ),
    inference(resolution,[],[f358,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f358,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,
    ( ~ spl3_2
    | spl3_35
    | ~ spl3_36
    | spl3_10
    | ~ spl3_3
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f352,f319,f86,f114,f357,f354,f82])).

fof(f319,plain,
    ( spl3_31
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | k2_waybel_0(X1,sK1,X0) = k4_yellow_6(X1,sK1)
        | ~ l1_waybel_0(sK1,X1)
        | ~ v1_yellow_6(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f352,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl3_3
    | ~ spl3_31 ),
    inference(resolution,[],[f320,f87])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( ~ v1_yellow_6(sK1,X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | k2_waybel_0(X1,sK1,X0) = k4_yellow_6(X1,sK1)
        | ~ l1_waybel_0(sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f319])).

fof(f321,plain,
    ( spl3_6
    | ~ spl3_5
    | spl3_31
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f317,f90,f319,f94,f98])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,X1)
        | ~ v1_yellow_6(sK1,X1)
        | k2_waybel_0(X1,sK1,X0) = k4_yellow_6(X1,sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f57,f91])).

fof(f91,plain,
    ( v7_waybel_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_6)).

fof(f280,plain,
    ( ~ spl3_2
    | spl3_25
    | ~ spl3_7
    | ~ spl3_9
    | spl3_10
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f272,f248,f86,f114,f110,f102,f275,f82])).

fof(f248,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ l1_waybel_0(sK1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(k4_yellow_6(X0,sK1),k10_yellow_6(X0,sK1))
        | ~ v1_yellow_6(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f272,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(resolution,[],[f249,f87])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ v1_yellow_6(sK1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(k4_yellow_6(X0,sK1),k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl3_6
    | ~ spl3_5
    | spl3_23
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f244,f90,f248,f94,f98])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,X0)
        | ~ v1_yellow_6(sK1,X0)
        | r2_hidden(k4_yellow_6(X0,sK1),k10_yellow_6(X0,sK1))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f64,f91])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

fof(f124,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f119,f122])).

fof(f119,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f118,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(X0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f117,f66])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f72,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,(
    ~ spl3_10 ),
    inference(avatar_split_clause,[],[f45,f114])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v1_yellow_6(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1)
          & l1_waybel_0(X1,sK0)
          & v1_yellow_6(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1)
        & l1_waybel_0(X1,sK0)
        & v1_yellow_6(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)
      & l1_waybel_0(sK1,sK0)
      & v1_yellow_6(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

fof(f112,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f51,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f86])).

fof(f52,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f53,f82])).

fof(f53,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f78])).

fof(f54,plain,(
    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (13760)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (13752)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (13760)Refutation not found, incomplete strategy% (13760)------------------------------
% 0.20/0.46  % (13760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (13760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (13760)Memory used [KB]: 10618
% 0.20/0.46  % (13760)Time elapsed: 0.013 s
% 0.20/0.46  % (13760)------------------------------
% 0.20/0.46  % (13760)------------------------------
% 0.20/0.47  % (13750)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (13752)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f475,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f96,f100,f104,f108,f112,f116,f124,f250,f280,f321,f359,f361,f370,f385,f407,f421,f453,f459,f471,f474])).
% 0.20/0.47  fof(f474,plain,(
% 0.20/0.47    ~spl3_37 | ~spl3_45),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f473])).
% 0.20/0.47  fof(f473,plain,(
% 0.20/0.47    $false | (~spl3_37 | ~spl3_45)),
% 0.20/0.47    inference(subsumption_resolution,[],[f406,f366])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl3_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f365])).
% 0.20/0.47  fof(f365,plain,(
% 0.20/0.47    spl3_37 <=> ! [X0] : ~m1_subset_1(X0,u1_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.47  fof(f406,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,u1_struct_0(sK1)) | ~spl3_45),
% 0.20/0.47    inference(avatar_component_clause,[],[f405])).
% 0.20/0.47  fof(f405,plain,(
% 0.20/0.47    spl3_45 <=> m1_subset_1(k1_xboole_0,u1_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.47  fof(f471,plain,(
% 0.20/0.47    ~spl3_38 | spl3_1 | ~spl3_25 | ~spl3_51),
% 0.20/0.47    inference(avatar_split_clause,[],[f461,f457,f275,f78,f368])).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    spl3_38 <=> m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_1 <=> k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f275,plain,(
% 0.20/0.47    spl3_25 <=> r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.47  fof(f457,plain,(
% 0.20/0.47    spl3_51 <=> ! [X0] : (k11_yellow_6(sK0,sK1) = X0 | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.47  fof(f461,plain,(
% 0.20/0.47    k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | (~spl3_25 | ~spl3_51)),
% 0.20/0.47    inference(resolution,[],[f458,f276])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~spl3_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f275])).
% 0.20/0.47  fof(f458,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_51),
% 0.20/0.47    inference(avatar_component_clause,[],[f457])).
% 0.20/0.47  fof(f459,plain,(
% 0.20/0.47    spl3_6 | ~spl3_5 | ~spl3_4 | ~spl3_2 | spl3_51 | ~spl3_3 | ~spl3_50),
% 0.20/0.47    inference(avatar_split_clause,[],[f454,f451,f86,f457,f82,f90,f94,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl3_6 <=> v2_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl3_5 <=> v4_orders_2(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl3_4 <=> v7_waybel_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_2 <=> l1_waybel_0(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl3_3 <=> v1_yellow_6(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f451,plain,(
% 0.20/0.47    spl3_50 <=> ! [X1,X0] : (k11_yellow_6(sK0,X0) = X1 | ~v1_yellow_6(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.47  fof(f454,plain,(
% 0.20/0.47    ( ! [X0] : (k11_yellow_6(sK0,sK1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)) ) | (~spl3_3 | ~spl3_50)),
% 0.20/0.47    inference(resolution,[],[f452,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    v1_yellow_6(sK1,sK0) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f452,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_yellow_6(X0,sK0) | k11_yellow_6(sK0,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_50),
% 0.20/0.47    inference(avatar_component_clause,[],[f451])).
% 0.20/0.47  fof(f453,plain,(
% 0.20/0.47    spl3_10 | ~spl3_9 | ~spl3_7 | spl3_50 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f449,f419,f451,f102,f110,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl3_10 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl3_9 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_7 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f419,plain,(
% 0.20/0.47    spl3_47 <=> ! [X1,X0] : (~r2_hidden(X0,k10_yellow_6(sK0,X1)) | k11_yellow_6(sK0,X1) = X0 | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,sK0) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.47  fof(f449,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k11_yellow_6(sK0,X0) = X1 | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_yellow_6(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_47),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f448])).
% 0.20/0.47  fof(f448,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k11_yellow_6(sK0,X0) = X1 | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_47),
% 0.20/0.47    inference(resolution,[],[f420,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | (~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_waybel_0(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => ((v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).
% 0.20/0.47  fof(f420,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v3_yellow_6(X1,sK0) | k11_yellow_6(sK0,X1) = X0 | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~r2_hidden(X0,k10_yellow_6(sK0,X1)) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f419])).
% 0.20/0.47  fof(f421,plain,(
% 0.20/0.47    spl3_10 | ~spl3_9 | ~spl3_7 | spl3_47 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f417,f106,f419,f102,f110,f114])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_8 <=> v8_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f417,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k10_yellow_6(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | k11_yellow_6(sK0,X1) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_8),
% 0.20/0.47    inference(resolution,[],[f59,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    v8_pre_topc(sK0) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v8_pre_topc(X0) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k11_yellow_6(X0,X1) = X2 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((k11_yellow_6(X0,X1) = X2 | ~r2_hidden(X2,k10_yellow_6(X0,X1))) & (r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).
% 0.20/0.47  fof(f407,plain,(
% 0.20/0.47    spl3_45 | ~spl3_11 | ~spl3_41),
% 0.20/0.47    inference(avatar_split_clause,[],[f400,f383,f122,f405])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl3_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    spl3_41 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.47  fof(f400,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,u1_struct_0(sK1)) | (~spl3_11 | ~spl3_41)),
% 0.20/0.47    inference(resolution,[],[f384,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | m1_subset_1(k1_xboole_0,X0)) ) | ~spl3_11),
% 0.20/0.47    inference(resolution,[],[f123,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f384,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK1)) | ~spl3_41),
% 0.20/0.47    inference(avatar_component_clause,[],[f383])).
% 0.20/0.47  fof(f385,plain,(
% 0.20/0.47    spl3_41 | ~spl3_37),
% 0.20/0.47    inference(avatar_split_clause,[],[f373,f365,f383])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK1)) | ~spl3_37),
% 0.20/0.47    inference(resolution,[],[f366,f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(resolution,[],[f68,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(rectify,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f370,plain,(
% 0.20/0.47    spl3_10 | ~spl3_36 | spl3_6 | ~spl3_2 | spl3_37 | spl3_38 | ~spl3_35),
% 0.20/0.47    inference(avatar_split_clause,[],[f363,f354,f368,f365,f82,f98,f357,f114])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    spl3_36 <=> l1_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.47  fof(f354,plain,(
% 0.20/0.47    spl3_35 <=> ! [X0] : (k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.47  fof(f363,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl3_35),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f362])).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl3_35),
% 0.20/0.47    inference(superposition,[],[f74,f355])).
% 0.20/0.47  fof(f355,plain,(
% 0.20/0.47    ( ! [X0] : (k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl3_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f354])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).
% 0.20/0.47  fof(f361,plain,(
% 0.20/0.47    ~spl3_7 | spl3_36),
% 0.20/0.47    inference(avatar_split_clause,[],[f360,f357,f102])).
% 0.20/0.47  fof(f360,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | spl3_36),
% 0.20/0.47    inference(resolution,[],[f358,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.47  fof(f358,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | spl3_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f357])).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    ~spl3_2 | spl3_35 | ~spl3_36 | spl3_10 | ~spl3_3 | ~spl3_31),
% 0.20/0.47    inference(avatar_split_clause,[],[f352,f319,f86,f114,f357,f354,f82])).
% 0.20/0.47  fof(f319,plain,(
% 0.20/0.47    spl3_31 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | k2_waybel_0(X1,sK1,X0) = k4_yellow_6(X1,sK1) | ~l1_waybel_0(sK1,X1) | ~v1_yellow_6(sK1,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.47  fof(f352,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~l1_struct_0(sK0) | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl3_3 | ~spl3_31)),
% 0.20/0.47    inference(resolution,[],[f320,f87])).
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_yellow_6(sK1,X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | k2_waybel_0(X1,sK1,X0) = k4_yellow_6(X1,sK1) | ~l1_waybel_0(sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl3_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f319])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    spl3_6 | ~spl3_5 | spl3_31 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f317,f90,f319,f94,f98])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,X1) | ~v1_yellow_6(sK1,X1) | k2_waybel_0(X1,sK1,X0) = k4_yellow_6(X1,sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_struct_0(X1) | v2_struct_0(X1)) ) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f57,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    v7_waybel_0(sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f90])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_6)).
% 0.20/0.47  fof(f280,plain,(
% 0.20/0.47    ~spl3_2 | spl3_25 | ~spl3_7 | ~spl3_9 | spl3_10 | ~spl3_3 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f272,f248,f86,f114,f110,f102,f275,f82])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    spl3_23 <=> ! [X0] : (~l1_waybel_0(sK1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r2_hidden(k4_yellow_6(X0,sK1),k10_yellow_6(X0,sK1)) | ~v1_yellow_6(sK1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | (~spl3_3 | ~spl3_23)),
% 0.20/0.47    inference(resolution,[],[f249,f87])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_yellow_6(sK1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r2_hidden(k4_yellow_6(X0,sK1),k10_yellow_6(X0,sK1)) | ~l1_waybel_0(sK1,X0)) ) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f248])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    spl3_6 | ~spl3_5 | spl3_23 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f244,f90,f248,f94,f98])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_waybel_0(sK1,X0) | ~v1_yellow_6(sK1,X0) | r2_hidden(k4_yellow_6(X0,sK1),k10_yellow_6(X0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f64,f91])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f119,f122])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(resolution,[],[f118,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(resolution,[],[f117,f66])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.47    inference(resolution,[],[f72,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f114])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    (k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) & l1_waybel_0(sK1,sK0) & v1_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f37,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1) & l1_waybel_0(X1,sK0) & v1_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ? [X1] : (k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1) & l1_waybel_0(X1,sK0) & v1_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) & l1_waybel_0(sK1,sK0) & v1_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f14])).
% 0.20/0.48  fof(f14,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f46,f110])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f47,f106])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    v8_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f48,f102])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f49,f98])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f50,f94])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    v4_orders_2(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f51,f90])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    v7_waybel_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f52,f86])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    v1_yellow_6(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f53,f82])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    l1_waybel_0(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f54,f78])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (13752)------------------------------
% 0.20/0.48  % (13752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13752)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (13752)Memory used [KB]: 10874
% 0.20/0.48  % (13752)Time elapsed: 0.015 s
% 0.20/0.48  % (13752)------------------------------
% 0.20/0.48  % (13752)------------------------------
% 0.20/0.48  % (13743)Success in time 0.12 s
%------------------------------------------------------------------------------
