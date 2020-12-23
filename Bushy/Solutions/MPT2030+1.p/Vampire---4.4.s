%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t29_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 272 expanded)
%              Number of leaves         :   22 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  702 (1332 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f108,f112,f116,f120,f124,f129,f133,f170,f175,f193,f281,f355,f403,f457,f539,f549])).

fof(f549,plain,
    ( spl13_1
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | spl13_21
    | ~ spl13_118 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_21
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f547,f174])).

fof(f174,plain,
    ( ~ r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl13_21
  <=> ~ r3_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f547,plain,
    ( r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f546,f115])).

fof(f115,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl13_7
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f546,plain,
    ( v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f545,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl13_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f545,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f544,f132])).

fof(f132,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl13_14
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f544,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f543,f103])).

fof(f103,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f543,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f542,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl13_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f542,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_8
    | ~ spl13_118 ),
    inference(subsumption_resolution,[],[f541,f119])).

fof(f119,plain,
    ( v2_pre_topc(sK0)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl13_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f541,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_118 ),
    inference(resolution,[],[f538,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => r2_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',d9_waybel_9)).

fof(f538,plain,
    ( r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_118 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl13_118
  <=> r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f539,plain,
    ( spl13_118
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f486,f455,f131,f127,f114,f110,f106,f102,f537])).

fof(f106,plain,
    ( spl13_2
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f110,plain,
    ( spl13_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f127,plain,
    ( spl13_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f455,plain,
    ( spl13_92
  <=> r1_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f486,plain,
    ( r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f485,f115])).

fof(f485,plain,
    ( v2_struct_0(sK0)
    | r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f484,f132])).

fof(f484,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f483,f111])).

fof(f111,plain,
    ( v7_waybel_0(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f483,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_12
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f482,f107])).

fof(f107,plain,
    ( v4_orders_2(sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f482,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_12
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f481,f103])).

fof(f481,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_12
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f480,f128])).

fof(f128,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f480,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_92 ),
    inference(resolution,[],[f456,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',t28_yellow_6)).

fof(f456,plain,
    ( r1_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f455])).

fof(f457,plain,
    ( spl13_92
    | ~ spl13_60
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f453,f401,f353,f455])).

fof(f353,plain,
    ( spl13_60
  <=> m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f401,plain,
    ( spl13_72
  <=> sP5(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f453,plain,
    ( r1_waybel_0(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl13_60
    | ~ spl13_72 ),
    inference(resolution,[],[f365,f402])).

fof(f402,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f401])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ sP5(sK2,X0,sK0)
        | r1_waybel_0(sK0,X0,sK3(sK0,sK1,sK2)) )
    | ~ spl13_60 ),
    inference(resolution,[],[f354,f81])).

fof(f81,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_connsp_2(X4,X0,X3)
      | r1_waybel_0(X0,X1,X4)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',d18_yellow_6)).

fof(f354,plain,
    ( m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK2)
    | ~ spl13_60 ),
    inference(avatar_component_clause,[],[f353])).

fof(f403,plain,
    ( spl13_72
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_26
    | ~ spl13_46 ),
    inference(avatar_split_clause,[],[f399,f279,f191,f168,f131,f122,f118,f114,f110,f106,f102,f401])).

fof(f191,plain,
    ( spl13_26
  <=> r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f279,plain,
    ( spl13_46
  <=> m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f399,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_26
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f398,f169])).

fof(f398,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_46 ),
    inference(resolution,[],[f307,f192])).

fof(f192,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f307,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
        | sP5(X1,sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f306,f115])).

fof(f306,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f305,f132])).

fof(f305,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f304,f111])).

fof(f304,plain,
    ( ! [X1] :
        ( ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f303,f107])).

fof(f303,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f302,f103])).

fof(f302,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f301,f123])).

fof(f301,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_8
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f292,f119])).

fof(f292,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP5(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_46 ),
    inference(resolution,[],[f280,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f280,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f279])).

fof(f355,plain,
    ( spl13_60
    | spl13_1
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | spl13_21 ),
    inference(avatar_split_clause,[],[f328,f173,f168,f131,f122,f118,f114,f102,f353])).

fof(f328,plain,
    ( m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK2)
    | ~ spl13_1
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f327,f174])).

fof(f327,plain,
    ( m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK2)
    | r3_waybel_9(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(resolution,[],[f162,f169])).

fof(f162,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(sK0,sK1,X2),sK0,X2)
        | r3_waybel_9(sK0,sK1,X2) )
    | ~ spl13_1
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f161,f115])).

fof(f161,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(sK0,sK1,X2),sK0,X2)
        | r3_waybel_9(sK0,sK1,X2) )
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f160,f103])).

fof(f160,plain,
    ( ! [X2] :
        ( v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(sK0,sK1,X2),sK0,X2)
        | r3_waybel_9(sK0,sK1,X2) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f159,f123])).

fof(f159,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(sK0,sK1,X2),sK0,X2)
        | r3_waybel_9(sK0,sK1,X2) )
    | ~ spl13_8
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f139,f119])).

fof(f139,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(sK0,sK1,X2),sK0,X2)
        | r3_waybel_9(sK0,sK1,X2) )
    | ~ spl13_14 ),
    inference(resolution,[],[f132,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(sK3(X0,X1,X2),X0,X2)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f281,plain,
    ( spl13_46
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f158,f131,f122,f118,f114,f110,f106,f102,f279])).

fof(f158,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f157,f115])).

fof(f157,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f156,f111])).

fof(f156,plain,
    ( ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f155,f107])).

fof(f155,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f154,f103])).

fof(f154,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f153,f123])).

fof(f153,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_8
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f138,f119])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_14 ),
    inference(resolution,[],[f132,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',dt_k10_yellow_6)).

fof(f193,plain,(
    spl13_26 ),
    inference(avatar_split_clause,[],[f60,f191])).

fof(f60,plain,(
    r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,X1))
                 => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',t29_waybel_9)).

fof(f175,plain,(
    ~ spl13_21 ),
    inference(avatar_split_clause,[],[f61,f173])).

fof(f61,plain,(
    ~ r3_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f170,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f59,f168])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f65,f131])).

fof(f65,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,
    ( spl13_12
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f125,f122,f127])).

fof(f125,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_10 ),
    inference(resolution,[],[f123,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',dt_l1_pre_topc)).

fof(f124,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f68,f122])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f120,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f67,f118])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    ~ spl13_7 ),
    inference(avatar_split_clause,[],[f66,f114])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f112,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f64,f110])).

fof(f64,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f63,f106])).

fof(f63,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f62,f102])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
