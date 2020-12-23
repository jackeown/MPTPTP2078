%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  296 ( 879 expanded)
%              Number of leaves         :   71 ( 463 expanded)
%              Depth                    :   11
%              Number of atoms          : 2350 (7518 expanded)
%              Number of equality atoms :   52 ( 134 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f184,f187,f194,f201,f217,f222,f227,f230,f246,f256,f263,f265,f267,f269,f271,f277,f281,f290,f292,f296,f308,f317,f320,f361,f366,f373,f381,f386,f391,f399,f410,f425,f429,f439,f440,f450])).

fof(f450,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | ~ spl10_35
    | ~ spl10_27
    | ~ spl10_55
    | ~ spl10_57 ),
    inference(avatar_split_clause,[],[f449,f423,f408,f241,f279,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f235,plain,
    ( spl10_25
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f170,plain,
    ( spl10_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f166,plain,
    ( spl10_15
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f142,plain,
    ( spl10_9
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f238,plain,
    ( spl10_26
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f134,plain,
    ( spl10_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f130,plain,
    ( spl10_6
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f126,plain,
    ( spl10_5
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f122,plain,
    ( spl10_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f279,plain,
    ( spl10_35
  <=> m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f241,plain,
    ( spl10_27
  <=> k1_waybel_2(sK0,sK1) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f408,plain,
    ( spl10_55
  <=> ! [X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f423,plain,
    ( spl10_57
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f449,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_27
    | ~ spl10_55
    | ~ spl10_57 ),
    inference(forward_demodulation,[],[f445,f242])).

fof(f242,plain,
    ( k1_waybel_2(sK0,sK1) = sK4(sK0,sK1)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f241])).

fof(f445,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_55
    | ~ spl10_57 ),
    inference(resolution,[],[f441,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

fof(f441,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_55
    | ~ spl10_57 ),
    inference(subsumption_resolution,[],[f424,f409])).

fof(f409,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1) )
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f408])).

fof(f424,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) )
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f423])).

fof(f440,plain,
    ( ~ spl10_4
    | spl10_50
    | ~ spl10_6
    | spl10_7
    | ~ spl10_5
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f432,f389,f126,f134,f130,f379,f122])).

fof(f379,plain,
    ( spl10_50
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f389,plain,
    ( spl10_52
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X1)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f432,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_5
    | ~ spl10_52 ),
    inference(resolution,[],[f390,f127])).

fof(f127,plain,
    ( v7_waybel_0(sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f390,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X1)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f389])).

fof(f439,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | ~ spl10_35
    | ~ spl10_27
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f438,f427,f241,f279,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f427,plain,
    ( spl10_58
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f438,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_27
    | ~ spl10_58 ),
    inference(forward_demodulation,[],[f434,f242])).

fof(f434,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_58 ),
    inference(resolution,[],[f428,f87])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f427])).

fof(f429,plain,
    ( ~ spl10_16
    | ~ spl10_15
    | ~ spl10_14
    | ~ spl10_13
    | ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_9
    | ~ spl10_8
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | ~ spl10_43
    | ~ spl10_3
    | spl10_58
    | ~ spl10_55 ),
    inference(avatar_split_clause,[],[f416,f408,f427,f118,f345,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170])).

fof(f162,plain,
    ( spl10_14
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f158,plain,
    ( spl10_13
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f154,plain,
    ( spl10_12
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f150,plain,
    ( spl10_11
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f146,plain,
    ( spl10_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f138,plain,
    ( spl10_8
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f345,plain,
    ( spl10_43
  <=> v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f118,plain,
    ( spl10_3
  <=> v10_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f416,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ v10_waybel_0(sK1,sK0)
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_55 ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ v10_waybel_0(sK1,sK0)
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_55 ),
    inference(resolution,[],[f409,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
                    & m1_subset_1(sK8(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v10_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).

fof(f425,plain,
    ( spl10_57
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_3
    | ~ spl10_47 ),
    inference(avatar_split_clause,[],[f421,f364,f118,f134,f130,f126,f122,f423])).

fof(f364,plain,
    ( spl10_47
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ v10_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f421,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl10_3
    | ~ spl10_47 ),
    inference(resolution,[],[f365,f119])).

fof(f119,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f365,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f364])).

fof(f410,plain,
    ( ~ spl10_12
    | ~ spl10_17
    | spl10_38
    | spl10_55
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f402,f397,f408,f312,f179,f154])).

fof(f179,plain,
    ( spl10_17
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f312,plain,
    ( spl10_38
  <=> r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f397,plain,
    ( spl10_53
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f402,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_53 ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_53 ),
    inference(resolution,[],[f398,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK6(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK6(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f398,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f397])).

fof(f399,plain,
    ( ~ spl10_12
    | ~ spl10_17
    | spl10_38
    | spl10_53
    | ~ spl10_39
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f395,f379,f315,f397,f312,f179,f154])).

fof(f315,plain,
    ( spl10_39
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_39
    | ~ spl10_50 ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_39
    | ~ spl10_50 ),
    inference(resolution,[],[f393,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0),u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) )
    | ~ spl10_39
    | ~ spl10_50 ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0),u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_39
    | ~ spl10_50 ),
    inference(resolution,[],[f380,f316])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f315])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) )
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f379])).

fof(f391,plain,
    ( ~ spl10_16
    | ~ spl10_15
    | ~ spl10_14
    | ~ spl10_13
    | ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_9
    | ~ spl10_8
    | spl10_52
    | spl10_51 ),
    inference(avatar_split_clause,[],[f387,f384,f389,f138,f142,f146,f150,f154,f158,f162,f166,f170])).

fof(f384,plain,
    ( spl10_51
  <=> m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f387,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X2)
        | r3_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl10_51 ),
    inference(resolution,[],[f385,f106])).

fof(f106,plain,(
    ! [X4,X0,X3,X1] :
      ( m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | r3_orders_2(X0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
                    & m1_subset_1(sK9(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r3_orders_2(X0,X3,X5) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).

fof(f385,plain,
    ( ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0))
    | spl10_51 ),
    inference(avatar_component_clause,[],[f384])).

fof(f386,plain,
    ( ~ spl10_51
    | spl10_49 ),
    inference(avatar_split_clause,[],[f382,f376,f384])).

fof(f376,plain,
    ( spl10_49
  <=> v5_pre_topc(k4_waybel_1(sK0,sK9(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f382,plain,
    ( ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0))
    | spl10_49 ),
    inference(resolution,[],[f377,f69])).

fof(f69,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

% (30121)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f39,plain,
    ( ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
      | ~ r1_waybel_9(sK0,sK1) )
    & v10_waybel_0(sK1,sK0)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & l1_waybel_9(sK0)
    & v1_compts_1(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
              | ~ r1_waybel_9(X0,X1) )
            & v10_waybel_0(X1,X0)
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1))
            | ~ r1_waybel_9(sK0,X1) )
          & v10_waybel_0(X1,sK0)
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v1_compts_1(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1))
          | ~ r1_waybel_9(sK0,X1) )
        & v10_waybel_0(X1,sK0)
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
        | ~ r1_waybel_9(sK0,sK1) )
      & v10_waybel_0(sK1,sK0)
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v10_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).

fof(f377,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK9(sK0)),sK0,sK0)
    | spl10_49 ),
    inference(avatar_component_clause,[],[f376])).

fof(f381,plain,
    ( ~ spl10_49
    | ~ spl10_4
    | ~ spl10_8
    | spl10_50
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_9
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f374,f371,f142,f170,f166,f162,f158,f154,f150,f146,f379,f138,f122,f376])).

fof(f371,plain,
    ( spl10_48
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r3_orders_2(X0,X2,X1)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f374,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ l1_waybel_9(sK0)
        | r3_orders_2(sK0,X1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK9(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_9
    | ~ spl10_48 ),
    inference(resolution,[],[f372,f143])).

fof(f143,plain,
    ( v1_compts_1(sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f372,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ l1_waybel_9(X0)
        | r3_orders_2(X0,X2,X1)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f371])).

fof(f373,plain,
    ( spl10_7
    | ~ spl10_6
    | spl10_48
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f369,f126,f371,f130,f134])).

fof(f369,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r3_orders_2(X0,X2,X1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f107,f127])).

fof(f107,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_orders_2(X0,X3,X4)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f366,plain,
    ( ~ spl10_16
    | ~ spl10_15
    | ~ spl10_14
    | ~ spl10_13
    | ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_9
    | ~ spl10_8
    | spl10_47
    | spl10_46 ),
    inference(avatar_split_clause,[],[f362,f359,f364,f138,f142,f146,f150,f154,f158,f162,f166,f170])).

fof(f359,plain,
    ( spl10_46
  <=> m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v10_waybel_0(X0,sK0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl10_46 ),
    inference(resolution,[],[f360,f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f360,plain,
    ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
    | spl10_46 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( ~ spl10_46
    | spl10_43 ),
    inference(avatar_split_clause,[],[f357,f345,f359])).

fof(f357,plain,
    ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
    | spl10_43 ),
    inference(resolution,[],[f346,f69])).

fof(f346,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
    | spl10_43 ),
    inference(avatar_component_clause,[],[f345])).

fof(f320,plain,
    ( ~ spl10_4
    | spl10_1
    | ~ spl10_8
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f318,f312,f138,f111,f122])).

fof(f111,plain,
    ( spl10_1
  <=> r1_waybel_9(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f318,plain,
    ( r1_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ spl10_8
    | ~ spl10_38 ),
    inference(resolution,[],[f313,f174])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)))
        | r1_waybel_9(sK0,X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f173,f139])).

fof(f139,plain,
    ( l1_waybel_9(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_9(X0)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1)
      | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ),
    inference(resolution,[],[f80,f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_waybel_9(X0,X1)
              | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r1_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_9)).

fof(f313,plain,
    ( r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f312])).

fof(f317,plain,
    ( ~ spl10_12
    | ~ spl10_17
    | spl10_38
    | spl10_39
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f310,f306,f315,f312,f179,f154])).

fof(f306,plain,
    ( spl10_37
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_37 ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_37 ),
    inference(resolution,[],[f307,f91])).

fof(f307,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) )
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f306])).

fof(f308,plain,
    ( spl10_25
    | ~ spl10_14
    | ~ spl10_17
    | spl10_37
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f300,f192,f306,f179,f162,f235])).

fof(f192,plain,
    ( spl10_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

% (30119)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f300,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1))
        | ~ m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_19 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1))
        | ~ m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_19 ),
    inference(resolution,[],[f193,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) )
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f296,plain,
    ( ~ spl10_35
    | ~ spl10_34
    | spl10_2
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f293,f248,f114,f275,f279])).

fof(f275,plain,
    ( spl10_34
  <=> r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f114,plain,
    ( spl10_2
  <=> r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f248,plain,
    ( spl10_29
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f293,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | spl10_2
    | ~ spl10_29 ),
    inference(resolution,[],[f249,f115])).

fof(f115,plain,
    ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f249,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f248])).

fof(f292,plain,
    ( ~ spl10_17
    | ~ spl10_11
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f291,f235,f150,f179])).

fof(f291,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_25 ),
    inference(resolution,[],[f236,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f236,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f235])).

fof(f290,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_29
    | ~ spl10_30
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f289,f258,f251,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f251,plain,
    ( spl10_30
  <=> k1_waybel_2(sK0,sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f258,plain,
    ( spl10_32
  <=> k1_waybel_2(sK0,sK1) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_30
    | ~ spl10_32 ),
    inference(trivial_inequality_removal,[],[f288])).

fof(f288,plain,
    ( ! [X0] :
        ( k1_waybel_2(sK0,sK1) != k1_waybel_2(sK0,sK1)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_30
    | ~ spl10_32 ),
    inference(forward_demodulation,[],[f285,f252])).

fof(f252,plain,
    ( k1_waybel_2(sK0,sK1) = sK2(sK0,sK1)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f251])).

fof(f285,plain,
    ( ! [X0] :
        ( k1_waybel_2(sK0,sK1) != sK2(sK0,sK1)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_32 ),
    inference(superposition,[],[f85,f259])).

fof(f259,plain,
    ( k1_waybel_2(sK0,sK1) = sK3(sK0,sK1)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f258])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1) != sK3(X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ( sK2(X0,X1) != sK3(X0,X1)
            & r3_waybel_9(X0,X1,sK3(X0,X1))
            & r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( X3 != X4
              & r3_waybel_9(X0,X1,X4)
              & r3_waybel_9(X0,X1,X3)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( sK2(X0,X1) != X4
            & r3_waybel_9(X0,X1,X4)
            & r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sK2(X0,X1) != X4
          & r3_waybel_9(X0,X1,X4)
          & r3_waybel_9(X0,X1,sK2(X0,X1))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sK2(X0,X1) != sK3(X0,X1)
        & r3_waybel_9(X0,X1,sK3(X0,X1))
        & r3_waybel_9(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ? [X3] :
              ( ? [X4] :
                  ( X3 != X4
                  & r3_waybel_9(X0,X1,X4)
                  & r3_waybel_9(X0,X1,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X4)
                 => r2_hidden(X4,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X2)
                 => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).

fof(f281,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_35
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f273,f241,f279,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f273,plain,
    ( m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_27 ),
    inference(superposition,[],[f86,f242])).

% (30138)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f277,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_34
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f272,f241,f275,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f272,plain,
    ( r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_27 ),
    inference(superposition,[],[f87,f242])).

fof(f271,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_29
    | spl10_33 ),
    inference(avatar_split_clause,[],[f270,f261,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f261,plain,
    ( spl10_33
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_33 ),
    inference(resolution,[],[f262,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f262,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl10_33 ),
    inference(avatar_component_clause,[],[f261])).

fof(f269,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_29
    | spl10_31 ),
    inference(avatar_split_clause,[],[f268,f254,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f254,plain,
    ( spl10_31
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_31 ),
    inference(resolution,[],[f255,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f255,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl10_31 ),
    inference(avatar_component_clause,[],[f254])).

fof(f267,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_28 ),
    inference(avatar_split_clause,[],[f266,f244,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f244,plain,
    ( spl10_28
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f266,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl10_28 ),
    inference(resolution,[],[f245,f86])).

fof(f245,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl10_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f265,plain,
    ( ~ spl10_8
    | spl10_26 ),
    inference(avatar_split_clause,[],[f264,f238,f138])).

fof(f264,plain,
    ( ~ l1_waybel_9(sK0)
    | spl10_26 ),
    inference(resolution,[],[f239,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f239,plain,
    ( ~ l1_pre_topc(sK0)
    | spl10_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f263,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_29
    | spl10_32
    | ~ spl10_33
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f233,f207,f261,f258,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f207,plain,
    ( spl10_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | k1_waybel_2(sK0,sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f233,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | k1_waybel_2(sK0,sK1) = sK3(sK0,sK1)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_22 ),
    inference(resolution,[],[f208,f84])).

% (30133)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_waybel_2(sK0,sK1) = X0 )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f207])).

fof(f256,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_29
    | spl10_30
    | ~ spl10_31
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f232,f207,f254,f251,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | k1_waybel_2(sK0,sK1) = sK2(sK0,sK1)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_22 ),
    inference(resolution,[],[f208,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,sK2(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f246,plain,
    ( spl10_25
    | ~ spl10_16
    | ~ spl10_15
    | ~ spl10_9
    | ~ spl10_26
    | spl10_7
    | ~ spl10_6
    | ~ spl10_5
    | ~ spl10_4
    | spl10_27
    | ~ spl10_28
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f231,f207,f244,f241,f122,f126,f130,f134,f238,f142,f166,f170,f235])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_2(sK0,sK1) = sK4(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_22 ),
    inference(resolution,[],[f208,f87])).

fof(f230,plain,
    ( ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_22
    | ~ spl10_3
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f228,f225,f118,f207,f134,f130,f126,f122])).

fof(f225,plain,
    ( spl10_24
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_2(sK0,X0) = X1
        | ~ v10_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_waybel_2(sK0,sK1) = X0
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl10_3
    | ~ spl10_24 ),
    inference(resolution,[],[f226,f119])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_2(sK0,X0) = X1
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f227,plain,
    ( ~ spl10_16
    | ~ spl10_15
    | ~ spl10_14
    | ~ spl10_13
    | ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_9
    | ~ spl10_8
    | spl10_24
    | spl10_23 ),
    inference(avatar_split_clause,[],[f223,f220,f225,f138,f142,f146,f150,f154,f158,f162,f166,f170])).

fof(f220,plain,
    ( spl10_23
  <=> m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v10_waybel_0(X0,sK0)
        | k1_waybel_2(sK0,X0) = X1
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl10_23 ),
    inference(resolution,[],[f221,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
      | k1_waybel_2(X0,X2) = X1
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
              | ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
                & m1_subset_1(sK7(X0),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v10_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).

fof(f221,plain,
    ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
    | spl10_23 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( ~ spl10_23
    | spl10_21 ),
    inference(avatar_split_clause,[],[f218,f204,f220])).

fof(f204,plain,
    ( spl10_21
  <=> v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f218,plain,
    ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
    | spl10_21 ),
    inference(resolution,[],[f205,f69])).

fof(f205,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f204])).

fof(f217,plain,
    ( ~ spl10_21
    | ~ spl10_4
    | spl10_22
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_3
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f202,f199,f118,f170,f166,f162,f158,f154,f150,f146,f142,f138,f207,f122,f204])).

fof(f199,plain,
    ( spl10_20
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(X0,sK1,X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_waybel_2(X0,sK1) = X1
        | ~ l1_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        | ~ v10_waybel_0(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_waybel_2(sK0,sK1) = X0
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl10_3
    | ~ spl10_20 ),
    inference(resolution,[],[f200,f119])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(sK1,X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_waybel_2(X0,sK1) = X1
        | ~ l1_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X1) )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( spl10_7
    | ~ spl10_6
    | spl10_20
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f195,f126,f199,f130,f134])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(X0,sK1,X1)
        | ~ v10_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        | ~ l1_waybel_0(sK1,X0)
        | k1_waybel_2(X0,sK1) = X1
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f95,f127])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X2)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
      | ~ l1_waybel_0(X2,X0)
      | k1_waybel_2(X0,X2) = X1
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f194,plain,
    ( ~ spl10_4
    | spl10_19
    | spl10_1
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f189,f182,f138,f111,f192,f122])).

fof(f182,plain,
    ( spl10_18
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))
        | ~ l1_waybel_0(sK1,sK0) )
    | spl10_1
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(resolution,[],[f188,f112])).

fof(f112,plain,
    ( ~ r1_waybel_9(sK0,sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( r1_waybel_9(sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)),X0)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)),X0))
        | ~ l1_waybel_0(X1,sK0) )
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(resolution,[],[f183,f174])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( r1_yellow_0(sK0,X1)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f187,plain,
    ( ~ spl10_8
    | spl10_17 ),
    inference(avatar_split_clause,[],[f185,f179,f138])).

fof(f185,plain,
    ( ~ l1_waybel_9(sK0)
    | spl10_17 ),
    inference(resolution,[],[f180,f77])).

fof(f180,plain,
    ( ~ l1_orders_2(sK0)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f184,plain,
    ( ~ spl10_17
    | spl10_18
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f177,f154,f182,f179])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,X1) )
    | ~ spl10_12 ),
    inference(resolution,[],[f93,f155])).

fof(f155,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f172,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f60,f170])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f168,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f61,f166])).

fof(f61,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f164,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f62,f162])).

fof(f62,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f160,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f63,f158])).

fof(f63,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f156,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f64,f154])).

fof(f64,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f152,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f65,f150])).

fof(f65,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f148,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f66,f146])).

fof(f66,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f144,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f67,f142])).

fof(f67,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f68,f138])).

fof(f68,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f136,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f70,f134])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f71,f130])).

fof(f71,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f72,f126])).

fof(f72,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f73,f122])).

fof(f73,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f74,f118])).

fof(f74,plain,(
    v10_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f75,f114,f111])).

fof(f75,plain,
    ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ r1_waybel_9(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (30129)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (30120)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (30117)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (30129)Refutation not found, incomplete strategy% (30129)------------------------------
% 0.21/0.48  % (30129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30129)Memory used [KB]: 10746
% 0.21/0.48  % (30129)Time elapsed: 0.083 s
% 0.21/0.48  % (30129)------------------------------
% 0.21/0.48  % (30129)------------------------------
% 0.21/0.48  % (30124)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (30132)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (30130)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (30123)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (30135)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (30125)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (30132)Refutation not found, incomplete strategy% (30132)------------------------------
% 0.21/0.49  % (30132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30132)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30132)Memory used [KB]: 10746
% 0.21/0.49  % (30132)Time elapsed: 0.012 s
% 0.21/0.49  % (30132)------------------------------
% 0.21/0.49  % (30132)------------------------------
% 0.21/0.50  % (30136)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (30122)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (30123)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f451,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f184,f187,f194,f201,f217,f222,f227,f230,f246,f256,f263,f265,f267,f269,f271,f277,f281,f290,f292,f296,f308,f317,f320,f361,f366,f373,f381,f386,f391,f399,f410,f425,f429,f439,f440,f450])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | ~spl10_35 | ~spl10_27 | ~spl10_55 | ~spl10_57),
% 0.21/0.50    inference(avatar_split_clause,[],[f449,f423,f408,f241,f279,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl10_25 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl10_16 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl10_15 <=> v8_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl10_9 <=> v1_compts_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    spl10_26 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl10_7 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl10_6 <=> v4_orders_2(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl10_5 <=> v7_waybel_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl10_4 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    spl10_35 <=> m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl10_27 <=> k1_waybel_2(sK0,sK1) = sK4(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    spl10_55 <=> ! [X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 0.21/0.50  fof(f423,plain,(
% 0.21/0.50    spl10_57 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 0.21/0.50  fof(f449,plain,(
% 0.21/0.50    ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_27 | ~spl10_55 | ~spl10_57)),
% 0.21/0.50    inference(forward_demodulation,[],[f445,f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK1) = sK4(sK0,sK1) | ~spl10_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f241])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_55 | ~spl10_57)),
% 0.21/0.50    inference(resolution,[],[f441,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl10_55 | ~spl10_57)),
% 0.21/0.50    inference(subsumption_resolution,[],[f424,f409])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1)) ) | ~spl10_55),
% 0.21/0.50    inference(avatar_component_clause,[],[f408])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) | ~spl10_57),
% 0.21/0.50    inference(avatar_component_clause,[],[f423])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    ~spl10_4 | spl10_50 | ~spl10_6 | spl10_7 | ~spl10_5 | ~spl10_52),
% 0.21/0.50    inference(avatar_split_clause,[],[f432,f389,f126,f134,f130,f379,f122])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    spl10_50 <=> ! [X1,X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    spl10_52 <=> ! [X1,X0,X2] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 0.21/0.50  fof(f432,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl10_5 | ~spl10_52)),
% 0.21/0.50    inference(resolution,[],[f390,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    v7_waybel_0(sK1) | ~spl10_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl10_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f389])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | ~spl10_35 | ~spl10_27 | ~spl10_58),
% 0.21/0.50    inference(avatar_split_clause,[],[f438,f427,f241,f279,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    spl10_58 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_27 | ~spl10_58)),
% 0.21/0.50    inference(forward_demodulation,[],[f434,f242])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl10_58),
% 0.21/0.50    inference(resolution,[],[f428,f87])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_58),
% 0.21/0.50    inference(avatar_component_clause,[],[f427])).
% 0.21/0.50  fof(f429,plain,(
% 0.21/0.50    ~spl10_16 | ~spl10_15 | ~spl10_14 | ~spl10_13 | ~spl10_12 | ~spl10_11 | ~spl10_10 | ~spl10_9 | ~spl10_8 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | ~spl10_43 | ~spl10_3 | spl10_58 | ~spl10_55),
% 0.21/0.50    inference(avatar_split_clause,[],[f416,f408,f427,f118,f345,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl10_14 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl10_13 <=> v4_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl10_12 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl10_11 <=> v1_lattice3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl10_10 <=> v2_lattice3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl10_8 <=> l1_waybel_9(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    spl10_43 <=> v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl10_3 <=> v10_waybel_0(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v10_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl10_55),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f413])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X0) | ~v10_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl10_55),
% 0.21/0.50    inference(resolution,[],[f409,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    spl10_57 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_3 | ~spl10_47),
% 0.21/0.50    inference(avatar_split_clause,[],[f421,f364,f118,f134,f130,f126,f122,f423])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    spl10_47 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~v10_waybel_0(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl10_3 | ~spl10_47)),
% 0.21/0.50    inference(resolution,[],[f365,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    v10_waybel_0(sK1,sK0) | ~spl10_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v10_waybel_0(X0,sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl10_47),
% 0.21/0.50    inference(avatar_component_clause,[],[f364])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    ~spl10_12 | ~spl10_17 | spl10_38 | spl10_55 | ~spl10_53),
% 0.21/0.50    inference(avatar_split_clause,[],[f402,f397,f408,f312,f179,f154])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    spl10_17 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    spl10_38 <=> r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    spl10_53 <=> ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl10_53),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f401])).
% 0.21/0.50  fof(f401,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl10_53),
% 0.21/0.50    inference(resolution,[],[f398,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,sK5(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,sK6(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f50,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,sK6(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(rectify,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_53),
% 0.21/0.50    inference(avatar_component_clause,[],[f397])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    ~spl10_12 | ~spl10_17 | spl10_38 | spl10_53 | ~spl10_39 | ~spl10_50),
% 0.21/0.50    inference(avatar_split_clause,[],[f395,f379,f315,f397,f312,f179,f154])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    spl10_39 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | (~spl10_39 | ~spl10_50)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f394])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | (~spl10_39 | ~spl10_50)),
% 0.21/0.50    inference(resolution,[],[f393,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f393,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) | (~spl10_39 | ~spl10_50)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f392])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl10_39 | ~spl10_50)),
% 0.21/0.50    inference(resolution,[],[f380,f316])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f315])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r3_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) | ~spl10_50),
% 0.21/0.50    inference(avatar_component_clause,[],[f379])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ~spl10_16 | ~spl10_15 | ~spl10_14 | ~spl10_13 | ~spl10_12 | ~spl10_11 | ~spl10_10 | ~spl10_9 | ~spl10_8 | spl10_52 | spl10_51),
% 0.21/0.50    inference(avatar_split_clause,[],[f387,f384,f389,f138,f142,f146,f150,f154,f158,f162,f166,f170])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    spl10_51 <=> m1_subset_1(sK9(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | r3_orders_2(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl10_51),
% 0.21/0.50    inference(resolution,[],[f385,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X4,X0,X3,X1] : (m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | r3_orders_2(X0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) & m1_subset_1(sK9(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f56,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(rectify,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.21/0.50    inference(rectify,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ~m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | spl10_51),
% 0.21/0.50    inference(avatar_component_clause,[],[f384])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    ~spl10_51 | spl10_49),
% 0.21/0.50    inference(avatar_split_clause,[],[f382,f376,f384])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    spl10_49 <=> v5_pre_topc(k4_waybel_1(sK0,sK9(sK0)),sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    ~m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | spl10_49),
% 0.21/0.50    inference(resolution,[],[f377,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  % (30121)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ((~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r1_waybel_9(sK0,sK1)) & v10_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1)) | ~r1_waybel_9(sK0,X1)) & v10_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X1] : ((~r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1)) | ~r1_waybel_9(sK0,X1)) & v10_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r1_waybel_9(sK0,sK1)) & v10_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(rectify,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v10_waybel_0(X2,X0) => (r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2))))))),
% 0.21/0.50    inference(rectify,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    ~v5_pre_topc(k4_waybel_1(sK0,sK9(sK0)),sK0,sK0) | spl10_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f376])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    ~spl10_49 | ~spl10_4 | ~spl10_8 | spl10_50 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_9 | ~spl10_48),
% 0.21/0.50    inference(avatar_split_clause,[],[f374,f371,f142,f170,f166,f162,f158,f154,f150,f146,f379,f138,f122,f376])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    spl10_48 <=> ! [X1,X0,X2] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r3_orders_2(X0,X2,X1) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~l1_waybel_9(sK0) | r3_orders_2(sK0,X1,X0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK9(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl10_9 | ~spl10_48)),
% 0.21/0.50    inference(resolution,[],[f372,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    v1_compts_1(sK0) | ~spl10_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~l1_waybel_9(X0) | r3_orders_2(X0,X2,X1) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X2) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl10_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f371])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    spl10_7 | ~spl10_6 | spl10_48 | ~spl10_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f369,f126,f371,f130,f134])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK1,X0) | r3_orders_2(X0,X2,X1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl10_5),
% 0.21/0.50    inference(resolution,[],[f107,f127])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r3_orders_2(X0,X3,X4) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f58])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    ~spl10_16 | ~spl10_15 | ~spl10_14 | ~spl10_13 | ~spl10_12 | ~spl10_11 | ~spl10_10 | ~spl10_9 | ~spl10_8 | spl10_47 | spl10_46),
% 0.21/0.50    inference(avatar_split_clause,[],[f362,f359,f364,f138,f142,f146,f150,f154,f158,f162,f166,f170])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    spl10_46 <=> m1_subset_1(sK8(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v10_waybel_0(X0,sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl10_46),
% 0.21/0.50    inference(resolution,[],[f360,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f55])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    ~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | spl10_46),
% 0.21/0.50    inference(avatar_component_clause,[],[f359])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    ~spl10_46 | spl10_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f357,f345,f359])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    ~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | spl10_43),
% 0.21/0.50    inference(resolution,[],[f346,f69])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | spl10_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f345])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~spl10_4 | spl10_1 | ~spl10_8 | ~spl10_38),
% 0.21/0.50    inference(avatar_split_clause,[],[f318,f312,f138,f111,f122])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl10_1 <=> r1_waybel_9(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    r1_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | (~spl10_8 | ~spl10_38)),
% 0.21/0.50    inference(resolution,[],[f313,f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_yellow_0(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0))) | r1_waybel_9(sK0,X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl10_8),
% 0.21/0.50    inference(resolution,[],[f173,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    l1_waybel_9(sK0) | ~spl10_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_9(X0) | ~l1_waybel_0(X1,X0) | r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) )),
% 0.21/0.50    inference(resolution,[],[f80,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | r1_waybel_9(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_9)).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl10_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f312])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    ~spl10_12 | ~spl10_17 | spl10_38 | spl10_39 | ~spl10_37),
% 0.21/0.50    inference(avatar_split_clause,[],[f310,f306,f315,f312,f179,f154])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    spl10_37 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0)) | ~r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl10_37),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f309])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl10_37),
% 0.21/0.50    inference(resolution,[],[f307,f91])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)) ) | ~spl10_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f306])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    spl10_25 | ~spl10_14 | ~spl10_17 | spl10_37 | ~spl10_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f300,f192,f306,f179,f162,f235])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl10_19 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.50  % (30119)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)) | ~m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl10_19),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f299])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~r3_orders_2(sK0,X1,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)) | ~m1_subset_1(sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl10_19),
% 0.21/0.50    inference(resolution,[],[f193,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) | ~spl10_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f192])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ~spl10_35 | ~spl10_34 | spl10_2 | ~spl10_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f293,f248,f114,f275,f279])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    spl10_34 <=> r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl10_2 <=> r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    spl10_29 <=> ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    ~r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | (spl10_2 | ~spl10_29)),
% 0.21/0.50    inference(resolution,[],[f249,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | spl10_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f248])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ~spl10_17 | ~spl10_11 | ~spl10_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f291,f235,f150,f179])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl10_25),
% 0.21/0.50    inference(resolution,[],[f236,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~spl10_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f235])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_29 | ~spl10_30 | ~spl10_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f289,f258,f251,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    spl10_30 <=> k1_waybel_2(sK0,sK1) = sK2(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl10_32 <=> k1_waybel_2(sK0,sK1) = sK3(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl10_30 | ~spl10_32)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ( ! [X0] : (k1_waybel_2(sK0,sK1) != k1_waybel_2(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl10_30 | ~spl10_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f285,f252])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK1) = sK2(sK0,sK1) | ~spl10_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f251])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    ( ! [X0] : (k1_waybel_2(sK0,sK1) != sK2(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl10_32),
% 0.21/0.50    inference(superposition,[],[f85,f259])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK1) = sK3(sK0,sK1) | ~spl10_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f258])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sK2(X0,X1) != sK3(X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) => (sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 0.21/0.50    inference(rectify,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_35 | ~spl10_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f273,f241,f279,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl10_27),
% 0.21/0.50    inference(superposition,[],[f86,f242])).
% 0.21/0.50  % (30138)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_34 | ~spl10_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f272,f241,f275,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl10_27),
% 0.21/0.50    inference(superposition,[],[f87,f242])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_29 | spl10_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f270,f261,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    spl10_33 <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl10_33),
% 0.21/0.50    inference(resolution,[],[f262,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | spl10_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f261])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_29 | spl10_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f268,f254,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    spl10_31 <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl10_31),
% 0.21/0.50    inference(resolution,[],[f255,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | spl10_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f254])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f266,f244,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    spl10_28 <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl10_28),
% 0.21/0.50    inference(resolution,[],[f245,f86])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | spl10_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f244])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~spl10_8 | spl10_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f264,f238,f138])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ~l1_waybel_9(sK0) | spl10_26),
% 0.21/0.50    inference(resolution,[],[f239,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | spl10_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f238])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_29 | spl10_32 | ~spl10_33 | ~spl10_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f233,f207,f261,f258,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl10_22 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | k1_waybel_2(sK0,sK1) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = sK3(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl10_22),
% 0.21/0.50    inference(resolution,[],[f208,f84])).
% 0.21/0.50  % (30133)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = X0) ) | ~spl10_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f207])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_29 | spl10_30 | ~spl10_31 | ~spl10_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f232,f207,f254,f251,f248,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = sK2(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl10_22),
% 0.21/0.50    inference(resolution,[],[f208,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,sK2(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    spl10_25 | ~spl10_16 | ~spl10_15 | ~spl10_9 | ~spl10_26 | spl10_7 | ~spl10_6 | ~spl10_5 | ~spl10_4 | spl10_27 | ~spl10_28 | ~spl10_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f231,f207,f244,f241,f122,f126,f130,f134,f238,f142,f166,f170,f235])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = sK4(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl10_22),
% 0.21/0.50    inference(resolution,[],[f208,f87])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | spl10_22 | ~spl10_3 | ~spl10_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f228,f225,f118,f207,f134,f130,f126,f122])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    spl10_24 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_waybel_2(sK0,X0) = X1 | ~v10_waybel_0(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_waybel_2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl10_3 | ~spl10_24)),
% 0.21/0.50    inference(resolution,[],[f226,f119])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v10_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_waybel_2(sK0,X0) = X1 | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl10_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f225])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    ~spl10_16 | ~spl10_15 | ~spl10_14 | ~spl10_13 | ~spl10_12 | ~spl10_11 | ~spl10_10 | ~spl10_9 | ~spl10_8 | spl10_24 | spl10_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f220,f225,f138,f142,f146,f150,f154,f158,f162,f166,f170])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl10_23 <=> m1_subset_1(sK7(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v10_waybel_0(X0,sK0) | k1_waybel_2(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl10_23),
% 0.21/0.50    inference(resolution,[],[f221,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | k1_waybel_2(X0,X2) = X1 | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_2(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | spl10_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f220])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ~spl10_23 | spl10_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f218,f204,f220])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl10_21 <=> v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | spl10_21),
% 0.21/0.50    inference(resolution,[],[f205,f69])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) | spl10_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f204])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ~spl10_21 | ~spl10_4 | spl10_22 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_3 | ~spl10_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f202,f199,f118,f170,f166,f162,f158,f154,f150,f146,f142,f138,f207,f122,f204])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl10_20 <=> ! [X1,X0] : (~r3_waybel_9(X0,sK1,X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_waybel_2(X0,sK1) = X1 | ~l1_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~v10_waybel_0(sK1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = X0 | ~l1_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl10_3 | ~spl10_20)),
% 0.21/0.51    inference(resolution,[],[f200,f119])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v10_waybel_0(sK1,X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_waybel_2(X0,sK1) = X1 | ~l1_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X1)) ) | ~spl10_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f199])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl10_7 | ~spl10_6 | spl10_20 | ~spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f195,f126,f199,f130,f134])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r3_waybel_9(X0,sK1,X1) | ~v10_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~l1_waybel_0(sK1,X0) | k1_waybel_2(X0,sK1) = X1 | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f95,f127])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v7_waybel_0(X2) | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | k1_waybel_2(X0,X2) = X1 | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ~spl10_4 | spl10_19 | spl10_1 | ~spl10_8 | ~spl10_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f189,f182,f138,f111,f192,f122])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl10_18 <=> ! [X1,X0] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | r1_yellow_0(sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) | ~l1_waybel_0(sK1,sK0)) ) | (spl10_1 | ~spl10_8 | ~spl10_18)),
% 0.21/0.51    inference(resolution,[],[f188,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~r1_waybel_9(sK0,sK1) | spl10_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_waybel_9(sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)),X0) | ~r1_orders_2(sK0,X0,sK5(sK0,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)),X0)) | ~l1_waybel_0(X1,sK0)) ) | (~spl10_8 | ~spl10_18)),
% 0.21/0.51    inference(resolution,[],[f183,f174])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_yellow_0(sK0,X1) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X1,X0)) ) | ~spl10_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f182])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~spl10_8 | spl10_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f185,f179,f138])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~l1_waybel_9(sK0) | spl10_17),
% 0.21/0.51    inference(resolution,[],[f180,f77])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | spl10_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f179])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~spl10_17 | spl10_18 | ~spl10_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f154,f182,f179])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | ~r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,X1)) ) | ~spl10_12),
% 0.21/0.51    inference(resolution,[],[f93,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    v5_orders_2(sK0) | ~spl10_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_yellow_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl10_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f170])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl10_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f166])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    v8_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl10_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f62,f162])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    v3_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl10_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f158])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v4_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl10_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f64,f154])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    v5_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl10_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f150])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v1_lattice3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl10_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f146])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v2_lattice3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    spl10_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f67,f142])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    v1_compts_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl10_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f138])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    l1_waybel_9(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~spl10_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f134])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f71,f130])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    v4_orders_2(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f72,f126])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    v7_waybel_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f73,f122])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    l1_waybel_0(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl10_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f74,f118])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    v10_waybel_0(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~spl10_1 | ~spl10_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f75,f114,f111])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r1_waybel_9(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (30123)------------------------------
% 0.21/0.51  % (30123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30123)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (30123)Memory used [KB]: 11001
% 0.21/0.51  % (30123)Time elapsed: 0.020 s
% 0.21/0.51  % (30123)------------------------------
% 0.21/0.51  % (30123)------------------------------
% 0.21/0.51  % (30113)Success in time 0.154 s
%------------------------------------------------------------------------------
