%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:39 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  175 (69721 expanded)
%              Number of leaves         :   35 (23099 expanded)
%              Depth                    :   23
%              Number of atoms          : 1293 (854309 expanded)
%              Number of equality atoms :   24 ( 316 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f141,f146,f151,f156,f160,f164,f1011,f1195])).

fof(f1195,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(avatar_contradiction_clause,[],[f1194])).

fof(f1194,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f85,f1191,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1191,plain,
    ( r2_hidden(sK6(sK0,sK1),k1_xboole_0)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(backward_demodulation,[],[f1028,f1188])).

fof(f1188,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK7(sK0,sK1,sK6(sK0,sK1)))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f1181,f1182,f1183,f1180,f1184,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k1_xboole_0 = k10_yellow_6(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k1_xboole_0 = k10_yellow_6(X0,X1) )
            & ( k1_xboole_0 != k10_yellow_6(X0,X1)
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f1184,plain,
    ( l1_waybel_0(sK7(sK0,sK1,sK6(sK0,sK1)),sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f1027,plain,
    ( m2_yellow_6(sK7(sK0,sK1,sK6(sK0,sK1)),sK0,sK1)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f155,f150,f145,f140,f1014,f1015,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK7(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2)))
                & m2_yellow_6(sK7(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2)))
        & m2_yellow_6(sK7(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
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
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f1015,plain,
    ( r3_waybel_9(sK0,sK1,sK6(sK0,sK1))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f131,f155,f150,f145,f140,f98])).

fof(f98,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK6(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK5(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK5(X0),X0)
            & v7_waybel_0(sK5(X0))
            & v4_orders_2(sK5(X0))
            & ~ v2_struct_0(sK5(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK6(X0,X3))
                & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f59,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK5(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK5(X0),X0)
        & v7_waybel_0(sK5(X0))
        & v4_orders_2(sK5(X0))
        & ~ v2_struct_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK6(X0,X3))
        & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).

fof(f131,plain,
    ( v1_compts_1(sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl12_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f1014,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f131,f155,f150,f145,f140,f97])).

fof(f97,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f140,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl12_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f145,plain,
    ( v7_waybel_0(sK1)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl12_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f150,plain,
    ( v4_orders_2(sK1)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl12_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f155,plain,
    ( ~ v2_struct_0(sK1)
    | spl12_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl12_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f165,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f77,f87])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1180,plain,
    ( ~ v3_yellow_6(sK7(sK0,sK1,sK6(sK0,sK1)),sK0)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f1027,f135])).

fof(f135,plain,
    ( ! [X2] :
        ( ~ m2_yellow_6(X2,sK0,sK1)
        | ~ v3_yellow_6(X2,sK0) )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl12_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1183,plain,
    ( v7_waybel_0(sK7(sK0,sK1,sK6(sK0,sK1)))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1182,plain,
    ( v4_orders_2(sK7(sK0,sK1,sK6(sK0,sK1)))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1181,plain,
    ( ~ v2_struct_0(sK7(sK0,sK1,sK6(sK0,sK1)))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,sK1) )
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK2(X3),sK0)
            & m2_yellow_6(sK2(X3),sK0,X3) )
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ v3_yellow_6(X2,X0)
                  | ~ m2_yellow_6(X2,X0,X1) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v3_yellow_6(X4,X0)
                  & m2_yellow_6(X4,X0,X3) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,sK0)
                | ~ m2_yellow_6(X2,sK0,X1) )
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK0)
                & m2_yellow_6(X4,sK0,X3) )
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v3_yellow_6(X2,sK0)
          | ~ m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1028,plain,
    ( r2_hidden(sK6(sK0,sK1),k10_yellow_6(sK0,sK7(sK0,sK1,sK6(sK0,sK1))))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f155,f150,f145,f140,f1014,f1015,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1011,plain,
    ( spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f85,f1004,f124])).

fof(f1004,plain,
    ( r2_hidden(sK8(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0)
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f86,f198,f568,f567,f113])).

fof(f113,plain,(
    ! [X2,X0,X5,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r1_waybel_0(X0,X1,X5)
      | ~ m1_connsp_2(X5,X0,sK8(X0,X1,X2))
      | r2_hidden(sK8(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X2))
                        & m1_connsp_2(sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) )
                      | ~ r2_hidden(sK8(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK8(X0,X1,X2)) )
                      | r2_hidden(sK8(X0,X1,X2),X2) )
                    & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK10(X0,X1,X6))
                            & m1_connsp_2(sK10(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f66,f69,f68,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK8(X0,X1,X2)) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK8(X0,X1,X2)) )
          | r2_hidden(sK8(X0,X1,X2),X2) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK8(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X2))
        & m1_connsp_2(sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK10(X0,X1,X6))
        & m1_connsp_2(sK10(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f567,plain,
    ( m1_connsp_2(sK10(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f199,f209,f566,f127])).

fof(f127,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK10(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK10(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f566,plain,
    ( ~ r2_hidden(sK8(sK0,sK2(sK3(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0))))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f209,f563,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f563,plain,
    ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f195,f209,f436,f276,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK11(X0,X1,X2))
                    & m1_connsp_2(sK11(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK11(X0,X1,X2))
        & m1_connsp_2(sK11(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( r2_waybel_0(X0,X1,X3)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

fof(f276,plain,
    ( m1_connsp_2(sK11(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f166,f169,f209,f262,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK11(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f262,plain,
    ( ~ r3_waybel_9(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f209,f96])).

fof(f96,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK3(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(sK3(X0),k6_yellow_6(X0))
            & l1_waybel_0(sK3(X0),X0)
            & v7_waybel_0(sK3(X0))
            & v4_orders_2(sK3(X0))
            & ~ v2_struct_0(sK3(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_hidden(X1,k6_yellow_6(X0))
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

fof(f132,plain,
    ( ~ v1_compts_1(sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f169,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f166,plain,
    ( ~ v2_struct_0(sK3(sK0))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f436,plain,
    ( ~ r2_waybel_0(sK0,sK2(sK3(sK0)),sK11(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f277,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f277,plain,
    ( ~ r2_waybel_0(sK0,sK3(sK0),sK11(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f166,f169,f209,f262,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK11(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f190,plain,
    ( m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0))
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f166,f168,f167,f169,f163])).

fof(f163,plain,
    ( ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl12_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f168,plain,
    ( v7_waybel_0(sK3(sK0))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f167,plain,
    ( v4_orders_2(sK3(sK0))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f209,plain,
    ( m1_subset_1(sK8(sK0,sK2(sK3(sK0)),k1_xboole_0),u1_struct_0(sK0))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f86,f198,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f199,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f568,plain,
    ( ~ r1_waybel_0(sK0,sK2(sK3(sK0)),sK10(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f199,f209,f566,f126])).

fof(f126,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK10(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK10(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f198,plain,
    ( k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0)))
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f188,f195,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f188,plain,
    ( v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl12_1
    | ~ spl12_7 ),
    inference(unit_resulting_resolution,[],[f166,f168,f167,f169,f159])).

fof(f159,plain,
    ( ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl12_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f195,plain,
    ( l1_waybel_0(sK2(sK3(sK0)),sK0)
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f122])).

fof(f194,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f121])).

fof(f193,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f120])).

fof(f192,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f119])).

fof(f164,plain,
    ( spl12_1
    | spl12_8 ),
    inference(avatar_split_clause,[],[f78,f162,f130])).

fof(f78,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f160,plain,
    ( spl12_1
    | spl12_7 ),
    inference(avatar_split_clause,[],[f79,f158,f130])).

fof(f79,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f156,plain,
    ( ~ spl12_1
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f80,f153,f130])).

fof(f80,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f151,plain,
    ( ~ spl12_1
    | spl12_5 ),
    inference(avatar_split_clause,[],[f81,f148,f130])).

fof(f81,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f146,plain,
    ( ~ spl12_1
    | spl12_4 ),
    inference(avatar_split_clause,[],[f82,f143,f130])).

fof(f82,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f141,plain,
    ( ~ spl12_1
    | spl12_3 ),
    inference(avatar_split_clause,[],[f83,f138,f130])).

fof(f83,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f136,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f84,f134,f130])).

fof(f84,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (30703)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (30710)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (30710)Refutation not found, incomplete strategy% (30710)------------------------------
% 0.21/0.48  % (30710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30710)Memory used [KB]: 6524
% 0.21/0.48  % (30710)Time elapsed: 0.058 s
% 0.21/0.48  % (30710)------------------------------
% 0.21/0.48  % (30710)------------------------------
% 0.21/0.49  % (30704)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (30700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (30697)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (30698)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (30695)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (30711)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (30712)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (30705)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (30696)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (30708)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (30714)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (30706)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (30705)Refutation not found, incomplete strategy% (30705)------------------------------
% 0.21/0.51  % (30705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30705)Memory used [KB]: 6396
% 0.21/0.51  % (30705)Time elapsed: 0.050 s
% 0.21/0.51  % (30705)------------------------------
% 0.21/0.51  % (30705)------------------------------
% 0.21/0.51  % (30699)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (30709)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (30715)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (30713)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (30715)Refutation not found, incomplete strategy% (30715)------------------------------
% 0.21/0.52  % (30715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30715)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30715)Memory used [KB]: 10618
% 0.21/0.52  % (30715)Time elapsed: 0.093 s
% 0.21/0.52  % (30715)------------------------------
% 0.21/0.52  % (30715)------------------------------
% 0.21/0.52  % (30702)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (30707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (30701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (30696)Refutation not found, incomplete strategy% (30696)------------------------------
% 0.21/0.52  % (30696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30696)Memory used [KB]: 10746
% 0.21/0.52  % (30696)Time elapsed: 0.083 s
% 0.21/0.52  % (30696)------------------------------
% 0.21/0.52  % (30696)------------------------------
% 1.63/0.61  % (30706)Refutation found. Thanks to Tanya!
% 1.63/0.61  % SZS status Theorem for theBenchmark
% 1.63/0.62  % SZS output start Proof for theBenchmark
% 1.63/0.62  fof(f1196,plain,(
% 1.63/0.62    $false),
% 1.63/0.62    inference(avatar_sat_refutation,[],[f136,f141,f146,f151,f156,f160,f164,f1011,f1195])).
% 1.63/0.62  fof(f1195,plain,(
% 1.63/0.62    ~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6),
% 1.63/0.62    inference(avatar_contradiction_clause,[],[f1194])).
% 1.63/0.62  fof(f1194,plain,(
% 1.63/0.62    $false | (~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f85,f1191,f124])).
% 1.63/0.62  fof(f124,plain,(
% 1.63/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f41])).
% 1.63/0.62  fof(f41,plain,(
% 1.63/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.63/0.62    inference(ennf_transformation,[],[f4])).
% 1.63/0.62  fof(f4,axiom,(
% 1.63/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.63/0.62  fof(f1191,plain,(
% 1.63/0.62    r2_hidden(sK6(sK0,sK1),k1_xboole_0) | (~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(backward_demodulation,[],[f1028,f1188])).
% 1.63/0.62  fof(f1188,plain,(
% 1.63/0.62    k1_xboole_0 = k10_yellow_6(sK0,sK7(sK0,sK1,sK6(sK0,sK1))) | (~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f1181,f1182,f1183,f1180,f1184,f105])).
% 1.63/0.62  fof(f105,plain,(
% 1.63/0.62    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f61])).
% 1.63/0.62  fof(f61,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(nnf_transformation,[],[f28])).
% 1.63/0.62  fof(f28,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f27])).
% 1.63/0.62  fof(f27,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f10])).
% 1.63/0.62  fof(f10,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 1.63/0.62  fof(f1184,plain,(
% 1.63/0.62    l1_waybel_0(sK7(sK0,sK1,sK6(sK0,sK1)),sK0) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f122])).
% 1.63/0.62  fof(f122,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f38])).
% 1.63/0.62  fof(f38,plain,(
% 1.63/0.62    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f37])).
% 1.63/0.62  fof(f37,plain,(
% 1.63/0.62    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f8])).
% 1.63/0.62  fof(f8,axiom,(
% 1.63/0.62    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 1.63/0.62  fof(f1027,plain,(
% 1.63/0.62    m2_yellow_6(sK7(sK0,sK1,sK6(sK0,sK1)),sK0,sK1) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f155,f150,f145,f140,f1014,f1015,f107])).
% 1.63/0.62  fof(f107,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (m2_yellow_6(sK7(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f63])).
% 1.63/0.62  fof(f63,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2))) & m2_yellow_6(sK7(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f62])).
% 1.63/0.62  fof(f62,plain,(
% 1.63/0.62    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2))) & m2_yellow_6(sK7(X0,X1,X2),X0,X1)))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f32,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f31])).
% 1.63/0.62  fof(f31,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f13])).
% 1.63/0.62  fof(f13,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 1.63/0.62  fof(f1015,plain,(
% 1.63/0.62    r3_waybel_9(sK0,sK1,sK6(sK0,sK1)) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f131,f155,f150,f145,f140,f98])).
% 1.63/0.62  fof(f98,plain,(
% 1.63/0.62    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK6(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f60])).
% 1.63/0.62  fof(f60,plain,(
% 1.63/0.62    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f59,f58])).
% 1.63/0.62  fof(f58,plain,(
% 1.63/0.62    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0))))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f59,plain,(
% 1.63/0.62    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f57,plain,(
% 1.63/0.62    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(rectify,[],[f56])).
% 1.63/0.62  fof(f56,plain,(
% 1.63/0.62    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(nnf_transformation,[],[f26])).
% 1.63/0.62  fof(f26,plain,(
% 1.63/0.62    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f25])).
% 1.63/0.62  fof(f25,plain,(
% 1.63/0.62    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f14])).
% 1.63/0.62  fof(f14,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).
% 1.63/0.62  fof(f131,plain,(
% 1.63/0.62    v1_compts_1(sK0) | ~spl12_1),
% 1.63/0.62    inference(avatar_component_clause,[],[f130])).
% 1.63/0.62  fof(f130,plain,(
% 1.63/0.62    spl12_1 <=> v1_compts_1(sK0)),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.63/0.62  fof(f1014,plain,(
% 1.63/0.62    m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0)) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f131,f155,f150,f145,f140,f97])).
% 1.63/0.62  fof(f97,plain,(
% 1.63/0.62    ( ! [X0,X3] : (m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f60])).
% 1.63/0.62  fof(f140,plain,(
% 1.63/0.62    l1_waybel_0(sK1,sK0) | ~spl12_3),
% 1.63/0.62    inference(avatar_component_clause,[],[f138])).
% 1.63/0.62  fof(f138,plain,(
% 1.63/0.62    spl12_3 <=> l1_waybel_0(sK1,sK0)),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.63/0.62  fof(f145,plain,(
% 1.63/0.62    v7_waybel_0(sK1) | ~spl12_4),
% 1.63/0.62    inference(avatar_component_clause,[],[f143])).
% 1.63/0.62  fof(f143,plain,(
% 1.63/0.62    spl12_4 <=> v7_waybel_0(sK1)),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.63/0.62  fof(f150,plain,(
% 1.63/0.62    v4_orders_2(sK1) | ~spl12_5),
% 1.63/0.62    inference(avatar_component_clause,[],[f148])).
% 1.63/0.62  fof(f148,plain,(
% 1.63/0.62    spl12_5 <=> v4_orders_2(sK1)),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.63/0.62  fof(f155,plain,(
% 1.63/0.62    ~v2_struct_0(sK1) | spl12_6),
% 1.63/0.62    inference(avatar_component_clause,[],[f153])).
% 1.63/0.62  fof(f153,plain,(
% 1.63/0.62    spl12_6 <=> v2_struct_0(sK1)),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.63/0.62  fof(f165,plain,(
% 1.63/0.62    l1_struct_0(sK0)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f77,f87])).
% 1.63/0.62  fof(f87,plain,(
% 1.63/0.62    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f20])).
% 1.63/0.62  fof(f20,plain,(
% 1.63/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.63/0.62    inference(ennf_transformation,[],[f5])).
% 1.63/0.62  fof(f5,axiom,(
% 1.63/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.63/0.62  fof(f1180,plain,(
% 1.63/0.62    ~v3_yellow_6(sK7(sK0,sK1,sK6(sK0,sK1)),sK0) | (~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f1027,f135])).
% 1.63/0.62  fof(f135,plain,(
% 1.63/0.62    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0)) ) | ~spl12_2),
% 1.63/0.62    inference(avatar_component_clause,[],[f134])).
% 1.63/0.62  fof(f134,plain,(
% 1.63/0.62    spl12_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.63/0.62  fof(f1183,plain,(
% 1.63/0.62    v7_waybel_0(sK7(sK0,sK1,sK6(sK0,sK1))) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f121])).
% 1.63/0.62  fof(f121,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f38])).
% 1.63/0.62  fof(f1182,plain,(
% 1.63/0.62    v4_orders_2(sK7(sK0,sK1,sK6(sK0,sK1))) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f120])).
% 1.63/0.62  fof(f120,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f38])).
% 1.63/0.62  fof(f1181,plain,(
% 1.63/0.62    ~v2_struct_0(sK7(sK0,sK1,sK6(sK0,sK1))) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f155,f150,f145,f140,f1027,f119])).
% 1.63/0.62  fof(f119,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f38])).
% 1.63/0.62  fof(f77,plain,(
% 1.63/0.62    l1_pre_topc(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f50,plain,(
% 1.63/0.62    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f49,f48,f47])).
% 1.63/0.62  fof(f47,plain,(
% 1.63/0.62    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f48,plain,(
% 1.63/0.62    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f49,plain,(
% 1.63/0.62    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f46,plain,(
% 1.63/0.62    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.63/0.62    inference(rectify,[],[f45])).
% 1.63/0.62  fof(f45,plain,(
% 1.63/0.62    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f44])).
% 1.63/0.62  fof(f44,plain,(
% 1.63/0.62    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.63/0.62    inference(nnf_transformation,[],[f19])).
% 1.63/0.62  fof(f19,plain,(
% 1.63/0.62    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f18])).
% 1.63/0.62  fof(f18,plain,(
% 1.63/0.62    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f17])).
% 1.63/0.62  fof(f17,negated_conjecture,(
% 1.63/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.63/0.62    inference(negated_conjecture,[],[f16])).
% 1.63/0.62  fof(f16,conjecture,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 1.63/0.62  fof(f76,plain,(
% 1.63/0.62    v2_pre_topc(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f75,plain,(
% 1.63/0.62    ~v2_struct_0(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f1028,plain,(
% 1.63/0.62    r2_hidden(sK6(sK0,sK1),k10_yellow_6(sK0,sK7(sK0,sK1,sK6(sK0,sK1)))) | (~spl12_1 | ~spl12_3 | ~spl12_4 | ~spl12_5 | spl12_6)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f155,f150,f145,f140,f1014,f1015,f108])).
% 1.63/0.62  fof(f108,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f63])).
% 1.63/0.62  fof(f85,plain,(
% 1.63/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f1])).
% 1.63/0.62  fof(f1,axiom,(
% 1.63/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.63/0.62  fof(f1011,plain,(
% 1.63/0.62    spl12_1 | ~spl12_7 | ~spl12_8),
% 1.63/0.62    inference(avatar_contradiction_clause,[],[f1010])).
% 1.63/0.62  fof(f1010,plain,(
% 1.63/0.62    $false | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f85,f1004,f124])).
% 1.63/0.62  fof(f1004,plain,(
% 1.63/0.62    r2_hidden(sK8(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f86,f198,f568,f567,f113])).
% 1.63/0.62  fof(f113,plain,(
% 1.63/0.62    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK8(X0,X1,X2)) | r2_hidden(sK8(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f70])).
% 1.63/0.62  fof(f70,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK9(X0,X1,X2)) & m1_connsp_2(sK9(X0,X1,X2),X0,sK8(X0,X1,X2))) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK8(X0,X1,X2))) | r2_hidden(sK8(X0,X1,X2),X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK10(X0,X1,X6)) & m1_connsp_2(sK10(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f66,f69,f68,f67])).
% 1.63/0.62  fof(f67,plain,(
% 1.63/0.62    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK8(X0,X1,X2))) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK8(X0,X1,X2))) | r2_hidden(sK8(X0,X1,X2),X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f68,plain,(
% 1.63/0.62    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK8(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK9(X0,X1,X2)) & m1_connsp_2(sK9(X0,X1,X2),X0,sK8(X0,X1,X2))))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f69,plain,(
% 1.63/0.62    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK10(X0,X1,X6)) & m1_connsp_2(sK10(X0,X1,X6),X0,X6)))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f66,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(rectify,[],[f65])).
% 1.63/0.62  fof(f65,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f64])).
% 1.63/0.62  fof(f64,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(nnf_transformation,[],[f34])).
% 1.63/0.62  fof(f34,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f33])).
% 1.63/0.62  fof(f33,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f6])).
% 1.63/0.62  fof(f6,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).
% 1.63/0.62  fof(f567,plain,(
% 1.63/0.62    m1_connsp_2(sK10(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f199,f209,f566,f127])).
% 1.63/0.62  fof(f127,plain,(
% 1.63/0.62    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK10(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(equality_resolution,[],[f110])).
% 1.63/0.62  fof(f110,plain,(
% 1.63/0.62    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK10(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f70])).
% 1.63/0.62  fof(f566,plain,(
% 1.63/0.62    ~r2_hidden(sK8(sK0,sK2(sK3(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0)))) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f209,f563,f106])).
% 1.63/0.62  fof(f106,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f30])).
% 1.63/0.62  fof(f30,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f29])).
% 1.63/0.62  fof(f29,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f12])).
% 1.63/0.62  fof(f12,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 1.63/0.62  fof(f563,plain,(
% 1.63/0.62    ~r3_waybel_9(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f195,f209,f436,f276,f116])).
% 1.63/0.62  fof(f116,plain,(
% 1.63/0.62    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f74])).
% 1.63/0.62  fof(f74,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | (~r2_waybel_0(X0,X1,sK11(X0,X1,X2)) & m1_connsp_2(sK11(X0,X1,X2),X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f72,f73])).
% 1.63/0.62  fof(f73,plain,(
% 1.63/0.62    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2)) => (~r2_waybel_0(X0,X1,sK11(X0,X1,X2)) & m1_connsp_2(sK11(X0,X1,X2),X0,X2)))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f72,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(rectify,[],[f71])).
% 1.63/0.62  fof(f71,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(nnf_transformation,[],[f36])).
% 1.63/0.62  fof(f36,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f35])).
% 1.63/0.62  fof(f35,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f11])).
% 1.63/0.62  fof(f11,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).
% 1.63/0.62  fof(f276,plain,(
% 1.63/0.62    m1_connsp_2(sK11(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f166,f169,f209,f262,f117])).
% 1.63/0.62  fof(f117,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | m1_connsp_2(sK11(X0,X1,X2),X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f74])).
% 1.63/0.62  fof(f262,plain,(
% 1.63/0.62    ~r3_waybel_9(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f209,f96])).
% 1.63/0.62  fof(f96,plain,(
% 1.63/0.62    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f55])).
% 1.63/0.62  fof(f55,plain,(
% 1.63/0.62    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK3(X0),k6_yellow_6(X0)) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f54,f53])).
% 1.63/0.62  fof(f53,plain,(
% 1.63/0.62    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK3(X0),k6_yellow_6(X0)) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f54,plain,(
% 1.63/0.62    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f52,plain,(
% 1.63/0.62    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(rectify,[],[f51])).
% 1.63/0.62  fof(f51,plain,(
% 1.63/0.62    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(nnf_transformation,[],[f24])).
% 1.63/0.62  fof(f24,plain,(
% 1.63/0.62    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f23])).
% 1.63/0.62  fof(f23,plain,(
% 1.63/0.62    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f15])).
% 1.63/0.62  fof(f15,axiom,(
% 1.63/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).
% 1.63/0.62  fof(f132,plain,(
% 1.63/0.62    ~v1_compts_1(sK0) | spl12_1),
% 1.63/0.62    inference(avatar_component_clause,[],[f130])).
% 1.63/0.62  fof(f169,plain,(
% 1.63/0.62    l1_waybel_0(sK3(sK0),sK0) | spl12_1),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f94])).
% 1.63/0.62  fof(f94,plain,(
% 1.63/0.62    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f55])).
% 1.63/0.62  fof(f166,plain,(
% 1.63/0.62    ~v2_struct_0(sK3(sK0)) | spl12_1),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f91])).
% 1.63/0.62  fof(f91,plain,(
% 1.63/0.62    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f55])).
% 1.63/0.62  fof(f436,plain,(
% 1.63/0.62    ~r2_waybel_0(sK0,sK2(sK3(sK0)),sK11(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f277,f88])).
% 1.63/0.62  fof(f88,plain,(
% 1.63/0.62    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f22])).
% 1.63/0.62  fof(f22,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f21])).
% 1.63/0.62  fof(f21,plain,(
% 1.63/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f9])).
% 1.63/0.62  fof(f9,axiom,(
% 1.63/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).
% 1.63/0.62  fof(f277,plain,(
% 1.63/0.62    ~r2_waybel_0(sK0,sK3(sK0),sK11(sK0,sK3(sK0),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f166,f169,f209,f262,f118])).
% 1.63/0.62  fof(f118,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_waybel_0(X0,X1,sK11(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f74])).
% 1.63/0.62  fof(f190,plain,(
% 1.63/0.62    m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0)) | (spl12_1 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f166,f168,f167,f169,f163])).
% 1.63/0.62  fof(f163,plain,(
% 1.63/0.62    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl12_8),
% 1.63/0.62    inference(avatar_component_clause,[],[f162])).
% 1.63/0.62  fof(f162,plain,(
% 1.63/0.62    spl12_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.63/0.62  fof(f168,plain,(
% 1.63/0.62    v7_waybel_0(sK3(sK0)) | spl12_1),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f93])).
% 1.63/0.62  fof(f93,plain,(
% 1.63/0.62    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f55])).
% 1.63/0.62  fof(f167,plain,(
% 1.63/0.62    v4_orders_2(sK3(sK0)) | spl12_1),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f132,f92])).
% 1.63/0.62  fof(f92,plain,(
% 1.63/0.62    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f55])).
% 1.63/0.62  fof(f209,plain,(
% 1.63/0.62    m1_subset_1(sK8(sK0,sK2(sK3(sK0)),k1_xboole_0),u1_struct_0(sK0)) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f86,f198,f112])).
% 1.63/0.62  fof(f112,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f70])).
% 1.63/0.62  fof(f199,plain,(
% 1.63/0.62    m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl12_1 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f123])).
% 1.63/0.62  fof(f123,plain,(
% 1.63/0.62    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f40])).
% 1.63/0.62  fof(f40,plain,(
% 1.63/0.62    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.62    inference(flattening,[],[f39])).
% 1.63/0.62  fof(f39,plain,(
% 1.63/0.62    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.62    inference(ennf_transformation,[],[f7])).
% 1.63/0.62  fof(f7,axiom,(
% 1.63/0.62    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.63/0.62  fof(f568,plain,(
% 1.63/0.62    ~r1_waybel_0(sK0,sK2(sK3(sK0)),sK10(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),k1_xboole_0))) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f195,f199,f209,f566,f126])).
% 1.63/0.62  fof(f126,plain,(
% 1.63/0.62    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK10(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(equality_resolution,[],[f111])).
% 1.63/0.62  fof(f111,plain,(
% 1.63/0.62    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK10(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f70])).
% 1.63/0.62  fof(f198,plain,(
% 1.63/0.62    k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0))) | (spl12_1 | ~spl12_7 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f76,f77,f192,f193,f194,f188,f195,f104])).
% 1.63/0.62  fof(f104,plain,(
% 1.63/0.62    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f61])).
% 1.63/0.62  fof(f188,plain,(
% 1.63/0.62    v3_yellow_6(sK2(sK3(sK0)),sK0) | (spl12_1 | ~spl12_7)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f166,f168,f167,f169,f159])).
% 1.63/0.62  fof(f159,plain,(
% 1.63/0.62    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl12_7),
% 1.63/0.62    inference(avatar_component_clause,[],[f158])).
% 1.63/0.62  fof(f158,plain,(
% 1.63/0.62    spl12_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 1.63/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.63/0.62  fof(f86,plain,(
% 1.63/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.63/0.62    inference(cnf_transformation,[],[f2])).
% 1.63/0.62  fof(f2,axiom,(
% 1.63/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.63/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.63/0.62  fof(f195,plain,(
% 1.63/0.62    l1_waybel_0(sK2(sK3(sK0)),sK0) | (spl12_1 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f122])).
% 1.63/0.62  fof(f194,plain,(
% 1.63/0.62    v7_waybel_0(sK2(sK3(sK0))) | (spl12_1 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f121])).
% 1.63/0.62  fof(f193,plain,(
% 1.63/0.62    v4_orders_2(sK2(sK3(sK0))) | (spl12_1 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f120])).
% 1.63/0.62  fof(f192,plain,(
% 1.63/0.62    ~v2_struct_0(sK2(sK3(sK0))) | (spl12_1 | ~spl12_8)),
% 1.63/0.62    inference(unit_resulting_resolution,[],[f75,f165,f166,f167,f168,f169,f190,f119])).
% 1.63/0.62  fof(f164,plain,(
% 1.63/0.62    spl12_1 | spl12_8),
% 1.63/0.62    inference(avatar_split_clause,[],[f78,f162,f130])).
% 1.63/0.62  fof(f78,plain,(
% 1.63/0.62    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f160,plain,(
% 1.63/0.62    spl12_1 | spl12_7),
% 1.63/0.62    inference(avatar_split_clause,[],[f79,f158,f130])).
% 1.63/0.62  fof(f79,plain,(
% 1.63/0.62    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f156,plain,(
% 1.63/0.62    ~spl12_1 | ~spl12_6),
% 1.63/0.62    inference(avatar_split_clause,[],[f80,f153,f130])).
% 1.63/0.62  fof(f80,plain,(
% 1.63/0.62    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f151,plain,(
% 1.63/0.62    ~spl12_1 | spl12_5),
% 1.63/0.62    inference(avatar_split_clause,[],[f81,f148,f130])).
% 1.63/0.62  fof(f81,plain,(
% 1.63/0.62    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f146,plain,(
% 1.63/0.62    ~spl12_1 | spl12_4),
% 1.63/0.62    inference(avatar_split_clause,[],[f82,f143,f130])).
% 1.63/0.62  fof(f82,plain,(
% 1.63/0.62    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f141,plain,(
% 1.63/0.62    ~spl12_1 | spl12_3),
% 1.63/0.62    inference(avatar_split_clause,[],[f83,f138,f130])).
% 1.63/0.62  fof(f83,plain,(
% 1.63/0.62    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  fof(f136,plain,(
% 1.63/0.62    ~spl12_1 | spl12_2),
% 1.63/0.62    inference(avatar_split_clause,[],[f84,f134,f130])).
% 1.63/0.62  fof(f84,plain,(
% 1.63/0.62    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f50])).
% 1.63/0.62  % SZS output end Proof for theBenchmark
% 1.63/0.62  % (30706)------------------------------
% 1.63/0.62  % (30706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.62  % (30706)Termination reason: Refutation
% 1.63/0.62  
% 1.63/0.62  % (30706)Memory used [KB]: 12281
% 1.63/0.62  % (30706)Time elapsed: 0.198 s
% 1.63/0.62  % (30706)------------------------------
% 1.63/0.62  % (30706)------------------------------
% 1.63/0.62  % (30694)Success in time 0.256 s
%------------------------------------------------------------------------------
