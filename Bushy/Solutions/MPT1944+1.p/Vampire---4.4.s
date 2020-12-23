%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t42_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 335 expanded)
%              Number of leaves         :   28 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          :  932 (1717 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f748,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f150,f157,f164,f171,f178,f185,f192,f240,f243,f363,f510,f669,f712,f724,f733,f747])).

fof(f747,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | spl13_21
    | ~ spl13_40
    | ~ spl13_80
    | ~ spl13_92 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_21
    | ~ spl13_40
    | ~ spl13_80
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f745,f239])).

fof(f239,plain,
    ( ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl13_21
  <=> ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f745,plain,
    ( r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_80
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f743,f654])).

fof(f654,plain,
    ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl13_80 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl13_80
  <=> m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f743,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_92 ),
    inference(resolution,[],[f723,f372])).

fof(f372,plain,
    ( ! [X0] :
        ( ~ sP4(X0,sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f371,f163])).

fof(f163,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl13_7
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f371,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f370,f191])).

fof(f191,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl13_14
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f369,f156])).

fof(f156,plain,
    ( v7_waybel_0(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl13_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f368,f149])).

fof(f149,plain,
    ( v4_orders_2(sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl13_2
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f367,f142])).

fof(f142,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f367,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f366,f177])).

fof(f177,plain,
    ( l1_pre_topc(sK0)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl13_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_8
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f364,f170])).

fof(f170,plain,
    ( v2_pre_topc(sK0)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl13_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl13_40 ),
    inference(resolution,[],[f362,f136])).

fof(f136,plain,(
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
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
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
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',d18_yellow_6)).

fof(f362,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl13_40
  <=> m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f723,plain,
    ( sP4(k4_yellow_6(sK0,sK1),sK1,sK0)
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f722])).

fof(f722,plain,
    ( spl13_92
  <=> sP4(k4_yellow_6(sK0,sK1),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f733,plain,(
    ~ spl13_66 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | ~ spl13_66 ),
    inference(resolution,[],[f509,f111])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',existence_m1_subset_1)).

fof(f509,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl13_66
  <=> ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f724,plain,
    ( spl13_92
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f714,f710,f722])).

fof(f710,plain,
    ( spl13_90
  <=> r1_waybel_0(sK0,sK1,sK5(sK0,sK1,k4_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f714,plain,
    ( sP4(k4_yellow_6(sK0,sK1),sK1,sK0)
    | ~ spl13_90 ),
    inference(resolution,[],[f711,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X3))
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f711,plain,
    ( r1_waybel_0(sK0,sK1,sK5(sK0,sK1,k4_yellow_6(sK0,sK1)))
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f710])).

fof(f712,plain,
    ( spl13_90
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | spl13_21
    | ~ spl13_40
    | ~ spl13_64
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f698,f653,f505,f361,f238,f190,f176,f169,f162,f155,f148,f141,f710])).

fof(f505,plain,
    ( spl13_64
  <=> ! [X1] :
        ( r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f698,plain,
    ( r1_waybel_0(sK0,sK1,sK5(sK0,sK1,k4_yellow_6(sK0,sK1)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_21
    | ~ spl13_40
    | ~ spl13_64
    | ~ spl13_80 ),
    inference(subsumption_resolution,[],[f526,f654])).

fof(f526,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | r1_waybel_0(sK0,sK1,sK5(sK0,sK1,k4_yellow_6(sK0,sK1)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_21
    | ~ spl13_40
    | ~ spl13_64 ),
    inference(subsumption_resolution,[],[f525,f239])).

fof(f525,plain,
    ( r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | r1_waybel_0(sK0,sK1,sK5(sK0,sK1,k4_yellow_6(sK0,sK1)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_64 ),
    inference(resolution,[],[f440,f506])).

fof(f506,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | r1_waybel_0(sK0,sK1,X1) )
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f505])).

fof(f440,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK5(sK0,sK1,X0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(duplicate_literal_removal,[],[f438])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | r2_hidden(X0,sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(resolution,[],[f372,f276])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( sP4(X0,X1,sK0)
        | r2_hidden(X0,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10 ),
    inference(resolution,[],[f273,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( m1_connsp_2(sK5(X0,X1,X3),X0,X3)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f273,plain,
    ( ! [X4,X3] :
        ( ~ m1_connsp_2(X3,sK0,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,X3) )
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f219,f217])).

fof(f217,plain,
    ( ! [X2,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X2,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f216,f163])).

fof(f216,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_connsp_2(X2,sK0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl13_8
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f212,f170])).

fof(f212,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_connsp_2(X2,sK0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl13_10 ),
    inference(resolution,[],[f177,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',dt_m1_connsp_2)).

fof(f219,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_connsp_2(X3,sK0,X4)
        | r2_hidden(X4,X3) )
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f218,f163])).

fof(f218,plain,
    ( ! [X4,X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_connsp_2(X3,sK0,X4)
        | r2_hidden(X4,X3) )
    | ~ spl13_8
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f213,f170])).

fof(f213,plain,
    ( ! [X4,X3] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_connsp_2(X3,sK0,X4)
        | r2_hidden(X4,X3) )
    | ~ spl13_10 ),
    inference(resolution,[],[f177,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',t6_connsp_2)).

fof(f669,plain,
    ( spl13_7
    | ~ spl13_14
    | ~ spl13_18
    | spl13_81 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_81 ),
    inference(subsumption_resolution,[],[f667,f163])).

fof(f667,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_81 ),
    inference(subsumption_resolution,[],[f666,f191])).

fof(f666,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_18
    | ~ spl13_81 ),
    inference(subsumption_resolution,[],[f665,f229])).

fof(f229,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl13_18
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f665,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_81 ),
    inference(resolution,[],[f657,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',dt_k4_yellow_6)).

fof(f657,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl13_81 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl13_81
  <=> ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_81])])).

fof(f510,plain,
    ( spl13_64
    | spl13_66
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f459,f228,f190,f183,f162,f155,f148,f141,f508,f505])).

fof(f183,plain,
    ( spl13_12
  <=> v1_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f459,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f458,f163])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f457,f191])).

fof(f457,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f456,f142])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f455,f229])).

fof(f455,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(duplicate_literal_removal,[],[f454])).

fof(f454,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,X1) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(resolution,[],[f399,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',d11_waybel_0)).

fof(f399,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X0)
        | ~ r2_hidden(k4_yellow_6(sK0,sK1),X0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f398,f142])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f395,f191])).

fof(f395,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(superposition,[],[f312,f306])).

fof(f306,plain,
    ( ! [X0] :
        ( k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f305,f229])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f304,f184])).

fof(f184,plain,
    ( v1_yellow_6(sK1,sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ v1_yellow_6(sK1,sK0)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f303,f163])).

fof(f303,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v1_yellow_6(sK1,sK0)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_14 ),
    inference(resolution,[],[f203,f191])).

fof(f203,plain,
    ( ! [X2,X1] :
        ( ~ l1_waybel_0(sK1,X1)
        | v2_struct_0(X1)
        | ~ v1_yellow_6(sK1,X1)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | k4_yellow_6(X1,sK1) = k2_waybel_0(X1,sK1,X2) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f202,f149])).

fof(f202,plain,
    ( ! [X2,X1] :
        ( ~ l1_struct_0(X1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X1)
        | ~ v1_yellow_6(sK1,X1)
        | ~ l1_waybel_0(sK1,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | k4_yellow_6(X1,sK1) = k2_waybel_0(X1,sK1,X2) )
    | ~ spl13_1
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f197,f142])).

fof(f197,plain,
    ( ! [X2,X1] :
        ( ~ l1_struct_0(X1)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X1)
        | ~ v1_yellow_6(sK1,X1)
        | ~ l1_waybel_0(sK1,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | k4_yellow_6(X1,sK1) = k2_waybel_0(X1,sK1,X2) )
    | ~ spl13_4 ),
    inference(resolution,[],[f156,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
             => k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',t25_yellow_6)).

fof(f312,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k2_waybel_0(sK0,X3,sK7(sK0,X3,X5,X4)),X5)
        | ~ l1_waybel_0(X3,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | v2_struct_0(X3)
        | r1_waybel_0(sK0,X3,X5) )
    | ~ spl13_7
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f209,f229])).

fof(f209,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r2_hidden(k2_waybel_0(sK0,X3,sK7(sK0,X3,X5,X4)),X5)
        | r1_waybel_0(sK0,X3,X5) )
    | ~ spl13_7 ),
    inference(resolution,[],[f163,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f363,plain,
    ( spl13_40
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f265,f190,f176,f169,f162,f155,f148,f141,f361])).

fof(f265,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f264,f170])).

fof(f264,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f263,f163])).

fof(f263,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f262,f177])).

fof(f262,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_14 ),
    inference(resolution,[],[f201,f191])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f200,f149])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl13_1
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f196,f142])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl13_4 ),
    inference(resolution,[],[f156,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',dt_k10_yellow_6)).

fof(f243,plain,
    ( ~ spl13_10
    | spl13_19 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl13_10
    | ~ spl13_19 ),
    inference(subsumption_resolution,[],[f241,f177])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl13_19 ),
    inference(resolution,[],[f232,f92])).

fof(f92,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',dt_l1_pre_topc)).

fof(f232,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl13_19
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f240,plain,(
    ~ spl13_21 ),
    inference(avatar_split_clause,[],[f87,f238])).

fof(f87,plain,(
    ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
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
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t42_yellow_6.p',t42_yellow_6)).

fof(f192,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f86,f190])).

fof(f86,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f185,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f85,f183])).

fof(f85,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f178,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f90,f176])).

fof(f90,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f171,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f89,f169])).

fof(f89,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f164,plain,(
    ~ spl13_7 ),
    inference(avatar_split_clause,[],[f88,f162])).

fof(f88,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f157,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f84,f155])).

fof(f84,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f150,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f83,f148])).

fof(f83,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f143,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f82,f141])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
