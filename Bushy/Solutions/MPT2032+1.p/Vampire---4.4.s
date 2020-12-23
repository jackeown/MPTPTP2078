%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t31_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  358 (1138 expanded)
%              Number of leaves         :  102 ( 579 expanded)
%              Depth                    :   10
%              Number of atoms          : 1241 (4254 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f135,f142,f149,f156,f163,f170,f177,f184,f191,f198,f205,f212,f219,f226,f236,f243,f250,f260,f274,f281,f288,f295,f307,f315,f325,f333,f341,f351,f358,f369,f377,f384,f393,f401,f411,f420,f441,f449,f457,f465,f473,f482,f489,f497,f505,f513,f522,f530,f538,f546,f555,f563,f571,f579,f588,f600,f607,f618,f625,f635,f643,f651,f658,f665,f676,f683,f690,f697,f704,f715,f723,f731])).

fof(f731,plain,
    ( spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_24
    | ~ spl12_26
    | ~ spl12_30
    | spl12_81
    | ~ spl12_100
    | ~ spl12_124
    | spl12_135 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_24
    | ~ spl12_26
    | ~ spl12_30
    | ~ spl12_81
    | ~ spl12_100
    | ~ spl12_124
    | ~ spl12_135 ),
    inference(subsumption_resolution,[],[f726,f705])).

fof(f705,plain,
    ( r2_waybel_0(sK0,sK2,sK5(sK0,sK1,sK3))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_26
    | ~ spl12_81
    | ~ spl12_100
    | ~ spl12_124 ),
    inference(unit_resulting_resolution,[],[f127,f134,f141,f464,f545,f218,f211,f650,f100])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK5(X0,X1,X2))
                    & m1_connsp_2(sK5(X0,X1,X2),X0,X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK5(X0,X1,X2))
        & m1_connsp_2(sK5(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
    inference(rectify,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',d9_waybel_9)).

fof(f650,plain,
    ( m1_connsp_2(sK5(sK0,sK1,sK3),sK0,sK3)
    | ~ spl12_124 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl12_124
  <=> m1_connsp_2(sK5(sK0,sK1,sK3),sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_124])])).

fof(f211,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl12_24
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f218,plain,
    ( r3_waybel_9(sK0,sK2,sK3)
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl12_26
  <=> r3_waybel_9(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f545,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl12_100 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl12_100
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_100])])).

fof(f464,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl12_81 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl12_81
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_81])])).

fof(f141,plain,
    ( l1_pre_topc(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f134,plain,
    ( v2_pre_topc(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl12_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f127,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl12_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f726,plain,
    ( ~ r2_waybel_0(sK0,sK2,sK5(sK0,sK1,sK3))
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30
    | ~ spl12_135 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f204,f689,f103])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',t27_yellow_6)).

fof(f689,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ spl12_135 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl12_135
  <=> ~ r2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_135])])).

fof(f204,plain,
    ( m2_yellow_6(sK2,sK0,sK1)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl12_22
  <=> m2_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f197,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl12_20
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f162,plain,
    ( v7_waybel_0(sK1)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl12_10
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f155,plain,
    ( v4_orders_2(sK1)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl12_8
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f148,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl12_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f235,plain,
    ( l1_struct_0(sK0)
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl12_30
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f723,plain,
    ( spl12_142
    | ~ spl12_140 ),
    inference(avatar_split_clause,[],[f716,f713,f721])).

fof(f721,plain,
    ( spl12_142
  <=> l1_struct_0(sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_142])])).

fof(f713,plain,
    ( spl12_140
  <=> l1_orders_2(sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_140])])).

fof(f716,plain,
    ( l1_struct_0(sK8(sK0,sK2))
    | ~ spl12_140 ),
    inference(unit_resulting_resolution,[],[f714,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',dt_l1_orders_2)).

fof(f714,plain,
    ( l1_orders_2(sK8(sK0,sK2))
    | ~ spl12_140 ),
    inference(avatar_component_clause,[],[f713])).

fof(f715,plain,
    ( spl12_140
    | ~ spl12_30
    | ~ spl12_138 ),
    inference(avatar_split_clause,[],[f707,f702,f234,f713])).

fof(f702,plain,
    ( spl12_138
  <=> l1_waybel_0(sK8(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_138])])).

fof(f707,plain,
    ( l1_orders_2(sK8(sK0,sK2))
    | ~ spl12_30
    | ~ spl12_138 ),
    inference(unit_resulting_resolution,[],[f235,f703,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',dt_l1_waybel_0)).

fof(f703,plain,
    ( l1_waybel_0(sK8(sK0,sK2),sK0)
    | ~ spl12_138 ),
    inference(avatar_component_clause,[],[f702])).

fof(f704,plain,
    ( spl12_138
    | spl12_1
    | ~ spl12_30
    | spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(avatar_split_clause,[],[f666,f656,f544,f503,f480,f463,f234,f126,f702])).

fof(f480,plain,
    ( spl12_84
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_84])])).

fof(f503,plain,
    ( spl12_90
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_90])])).

fof(f656,plain,
    ( spl12_126
  <=> m2_yellow_6(sK8(sK0,sK2),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_126])])).

fof(f666,plain,
    ( l1_waybel_0(sK8(sK0,sK2),sK0)
    | ~ spl12_1
    | ~ spl12_30
    | ~ spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(unit_resulting_resolution,[],[f127,f235,f464,f481,f504,f545,f657,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',dt_m2_yellow_6)).

fof(f657,plain,
    ( m2_yellow_6(sK8(sK0,sK2),sK0,sK2)
    | ~ spl12_126 ),
    inference(avatar_component_clause,[],[f656])).

fof(f504,plain,
    ( v7_waybel_0(sK2)
    | ~ spl12_90 ),
    inference(avatar_component_clause,[],[f503])).

fof(f481,plain,
    ( v4_orders_2(sK2)
    | ~ spl12_84 ),
    inference(avatar_component_clause,[],[f480])).

fof(f697,plain,
    ( ~ spl12_137
    | spl12_1
    | ~ spl12_30
    | spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(avatar_split_clause,[],[f669,f656,f544,f503,f480,f463,f234,f126,f695])).

fof(f695,plain,
    ( spl12_137
  <=> ~ v2_struct_0(sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_137])])).

fof(f669,plain,
    ( ~ v2_struct_0(sK8(sK0,sK2))
    | ~ spl12_1
    | ~ spl12_30
    | ~ spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(unit_resulting_resolution,[],[f127,f235,f464,f481,f504,f545,f657,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f690,plain,
    ( ~ spl12_135
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_7
    | ~ spl12_20
    | ~ spl12_24
    | spl12_29 ),
    inference(avatar_split_clause,[],[f608,f224,f210,f196,f147,f140,f133,f126,f688])).

fof(f224,plain,
    ( spl12_29
  <=> ~ r3_waybel_9(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f608,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_29 ),
    inference(unit_resulting_resolution,[],[f127,f134,f141,f148,f197,f225,f211,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_waybel_0(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r3_waybel_9(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f225,plain,
    ( ~ r3_waybel_9(sK0,sK1,sK3)
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f224])).

fof(f683,plain,
    ( spl12_132
    | spl12_1
    | ~ spl12_30
    | spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(avatar_split_clause,[],[f668,f656,f544,f503,f480,f463,f234,f126,f681])).

fof(f681,plain,
    ( spl12_132
  <=> v4_orders_2(sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_132])])).

fof(f668,plain,
    ( v4_orders_2(sK8(sK0,sK2))
    | ~ spl12_1
    | ~ spl12_30
    | ~ spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(unit_resulting_resolution,[],[f127,f235,f464,f481,f504,f545,f657,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f676,plain,
    ( spl12_130
    | spl12_1
    | ~ spl12_30
    | spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(avatar_split_clause,[],[f667,f656,f544,f503,f480,f463,f234,f126,f674])).

fof(f674,plain,
    ( spl12_130
  <=> v7_waybel_0(sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_130])])).

fof(f667,plain,
    ( v7_waybel_0(sK8(sK0,sK2))
    | ~ spl12_1
    | ~ spl12_30
    | ~ spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100
    | ~ spl12_126 ),
    inference(unit_resulting_resolution,[],[f127,f235,f464,f481,f504,f545,f657,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f665,plain,
    ( spl12_128
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_26
    | ~ spl12_78
    | spl12_81
    | ~ spl12_100 ),
    inference(avatar_split_clause,[],[f626,f544,f463,f455,f217,f210,f140,f133,f126,f663])).

fof(f663,plain,
    ( spl12_128
  <=> r2_waybel_0(sK0,sK2,sK7(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_128])])).

fof(f455,plain,
    ( spl12_78
  <=> m1_connsp_2(sK7(sK0,sK3),sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_78])])).

fof(f626,plain,
    ( r2_waybel_0(sK0,sK2,sK7(sK0,sK3))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_26
    | ~ spl12_78
    | ~ spl12_81
    | ~ spl12_100 ),
    inference(unit_resulting_resolution,[],[f127,f134,f141,f464,f545,f218,f456,f211,f100])).

fof(f456,plain,
    ( m1_connsp_2(sK7(sK0,sK3),sK0,sK3)
    | ~ spl12_78 ),
    inference(avatar_component_clause,[],[f455])).

fof(f658,plain,
    ( spl12_126
    | spl12_1
    | ~ spl12_30
    | spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100 ),
    inference(avatar_split_clause,[],[f547,f544,f503,f480,f463,f234,f126,f656])).

fof(f547,plain,
    ( m2_yellow_6(sK8(sK0,sK2),sK0,sK2)
    | ~ spl12_1
    | ~ spl12_30
    | ~ spl12_81
    | ~ spl12_84
    | ~ spl12_90
    | ~ spl12_100 ),
    inference(unit_resulting_resolution,[],[f127,f235,f464,f481,f504,f545,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m2_yellow_6(sK8(X0,X1),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m2_yellow_6(sK8(X0,X1),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f54,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_yellow_6(X2,X0,X1)
     => m2_yellow_6(sK8(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_yellow_6(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_m2_yellow_6)).

fof(f651,plain,
    ( spl12_124
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_7
    | ~ spl12_20
    | ~ spl12_24
    | spl12_29 ),
    inference(avatar_split_clause,[],[f581,f224,f210,f196,f147,f140,f133,f126,f649])).

fof(f581,plain,
    ( m1_connsp_2(sK5(sK0,sK1,sK3),sK0,sK3)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_29 ),
    inference(unit_resulting_resolution,[],[f127,f134,f141,f148,f197,f225,f211,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f643,plain,
    ( spl12_122
    | ~ spl12_120 ),
    inference(avatar_split_clause,[],[f636,f633,f641])).

fof(f641,plain,
    ( spl12_122
  <=> l1_struct_0(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_122])])).

fof(f633,plain,
    ( spl12_120
  <=> l1_orders_2(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_120])])).

fof(f636,plain,
    ( l1_struct_0(sK8(sK0,sK1))
    | ~ spl12_120 ),
    inference(unit_resulting_resolution,[],[f634,f95])).

fof(f634,plain,
    ( l1_orders_2(sK8(sK0,sK1))
    | ~ spl12_120 ),
    inference(avatar_component_clause,[],[f633])).

fof(f635,plain,
    ( spl12_120
    | ~ spl12_30
    | ~ spl12_118 ),
    inference(avatar_split_clause,[],[f627,f623,f234,f633])).

fof(f623,plain,
    ( spl12_118
  <=> l1_waybel_0(sK8(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_118])])).

fof(f627,plain,
    ( l1_orders_2(sK8(sK0,sK1))
    | ~ spl12_30
    | ~ spl12_118 ),
    inference(unit_resulting_resolution,[],[f235,f624,f98])).

fof(f624,plain,
    ( l1_waybel_0(sK8(sK0,sK1),sK0)
    | ~ spl12_118 ),
    inference(avatar_component_clause,[],[f623])).

fof(f625,plain,
    ( spl12_118
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(avatar_split_clause,[],[f590,f536,f234,f196,f161,f154,f147,f126,f623])).

fof(f536,plain,
    ( spl12_98
  <=> m2_yellow_6(sK8(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_98])])).

fof(f590,plain,
    ( l1_waybel_0(sK8(sK0,sK1),sK0)
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f537,f113])).

fof(f537,plain,
    ( m2_yellow_6(sK8(sK0,sK1),sK0,sK1)
    | ~ spl12_98 ),
    inference(avatar_component_clause,[],[f536])).

fof(f618,plain,
    ( ~ spl12_117
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(avatar_split_clause,[],[f593,f536,f234,f196,f161,f154,f147,f126,f616])).

fof(f616,plain,
    ( spl12_117
  <=> ~ v2_struct_0(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_117])])).

fof(f593,plain,
    ( ~ v2_struct_0(sK8(sK0,sK1))
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f537,f110])).

fof(f607,plain,
    ( spl12_114
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(avatar_split_clause,[],[f592,f536,f234,f196,f161,f154,f147,f126,f605])).

fof(f605,plain,
    ( spl12_114
  <=> v4_orders_2(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_114])])).

fof(f592,plain,
    ( v4_orders_2(sK8(sK0,sK1))
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f537,f111])).

fof(f600,plain,
    ( spl12_112
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(avatar_split_clause,[],[f591,f536,f234,f196,f161,f154,f147,f126,f598])).

fof(f598,plain,
    ( spl12_112
  <=> v7_waybel_0(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_112])])).

fof(f591,plain,
    ( v7_waybel_0(sK8(sK0,sK1))
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_98 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f537,f112])).

fof(f588,plain,
    ( spl12_110
    | ~ spl12_108 ),
    inference(avatar_split_clause,[],[f580,f577,f586])).

fof(f586,plain,
    ( spl12_110
  <=> l1_struct_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_110])])).

fof(f577,plain,
    ( spl12_108
  <=> l1_orders_2(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_108])])).

fof(f580,plain,
    ( l1_struct_0(sK4(sK2))
    | ~ spl12_108 ),
    inference(unit_resulting_resolution,[],[f578,f95])).

fof(f578,plain,
    ( l1_orders_2(sK4(sK2))
    | ~ spl12_108 ),
    inference(avatar_component_clause,[],[f577])).

fof(f579,plain,
    ( spl12_108
    | ~ spl12_104
    | ~ spl12_106 ),
    inference(avatar_split_clause,[],[f572,f569,f561,f577])).

fof(f561,plain,
    ( spl12_104
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_104])])).

fof(f569,plain,
    ( spl12_106
  <=> l1_waybel_0(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_106])])).

fof(f572,plain,
    ( l1_orders_2(sK4(sK2))
    | ~ spl12_104
    | ~ spl12_106 ),
    inference(unit_resulting_resolution,[],[f562,f570,f98])).

fof(f570,plain,
    ( l1_waybel_0(sK4(sK2),sK2)
    | ~ spl12_106 ),
    inference(avatar_component_clause,[],[f569])).

fof(f562,plain,
    ( l1_struct_0(sK2)
    | ~ spl12_104 ),
    inference(avatar_component_clause,[],[f561])).

fof(f571,plain,
    ( spl12_106
    | ~ spl12_104 ),
    inference(avatar_split_clause,[],[f564,f561,f569])).

fof(f564,plain,
    ( l1_waybel_0(sK4(sK2),sK2)
    | ~ spl12_104 ),
    inference(unit_resulting_resolution,[],[f562,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_l1_waybel_0)).

fof(f563,plain,
    ( spl12_104
    | ~ spl12_102 ),
    inference(avatar_split_clause,[],[f556,f553,f561])).

fof(f553,plain,
    ( spl12_102
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_102])])).

fof(f556,plain,
    ( l1_struct_0(sK2)
    | ~ spl12_102 ),
    inference(unit_resulting_resolution,[],[f554,f95])).

fof(f554,plain,
    ( l1_orders_2(sK2)
    | ~ spl12_102 ),
    inference(avatar_component_clause,[],[f553])).

fof(f555,plain,
    ( spl12_102
    | ~ spl12_30
    | ~ spl12_100 ),
    inference(avatar_split_clause,[],[f548,f544,f234,f553])).

fof(f548,plain,
    ( l1_orders_2(sK2)
    | ~ spl12_30
    | ~ spl12_100 ),
    inference(unit_resulting_resolution,[],[f235,f545,f98])).

fof(f546,plain,
    ( spl12_100
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f539,f234,f203,f196,f161,f154,f147,f126,f544])).

fof(f539,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f204,f113])).

fof(f538,plain,
    ( spl12_98
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f515,f234,f196,f161,f154,f147,f126,f536])).

fof(f515,plain,
    ( m2_yellow_6(sK8(sK0,sK1),sK0,sK1)
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f114])).

fof(f530,plain,
    ( spl12_96
    | ~ spl12_94 ),
    inference(avatar_split_clause,[],[f523,f520,f528])).

fof(f528,plain,
    ( spl12_96
  <=> l1_struct_0(sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_96])])).

fof(f520,plain,
    ( spl12_94
  <=> l1_orders_2(sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_94])])).

fof(f523,plain,
    ( l1_struct_0(sK4(sK4(sK0)))
    | ~ spl12_94 ),
    inference(unit_resulting_resolution,[],[f521,f95])).

fof(f521,plain,
    ( l1_orders_2(sK4(sK4(sK0)))
    | ~ spl12_94 ),
    inference(avatar_component_clause,[],[f520])).

fof(f522,plain,
    ( spl12_94
    | ~ spl12_60
    | ~ spl12_92 ),
    inference(avatar_split_clause,[],[f514,f511,f367,f520])).

fof(f367,plain,
    ( spl12_60
  <=> l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_60])])).

fof(f511,plain,
    ( spl12_92
  <=> l1_waybel_0(sK4(sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_92])])).

fof(f514,plain,
    ( l1_orders_2(sK4(sK4(sK0)))
    | ~ spl12_60
    | ~ spl12_92 ),
    inference(unit_resulting_resolution,[],[f368,f512,f98])).

fof(f512,plain,
    ( l1_waybel_0(sK4(sK4(sK0)),sK4(sK0))
    | ~ spl12_92 ),
    inference(avatar_component_clause,[],[f511])).

fof(f368,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl12_60 ),
    inference(avatar_component_clause,[],[f367])).

fof(f513,plain,
    ( spl12_92
    | ~ spl12_60 ),
    inference(avatar_split_clause,[],[f370,f367,f511])).

fof(f370,plain,
    ( l1_waybel_0(sK4(sK4(sK0)),sK4(sK0))
    | ~ spl12_60 ),
    inference(unit_resulting_resolution,[],[f368,f99])).

fof(f505,plain,
    ( spl12_90
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f498,f234,f203,f196,f161,f154,f147,f126,f503])).

fof(f498,plain,
    ( v7_waybel_0(sK2)
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f204,f112])).

fof(f497,plain,
    ( spl12_88
    | ~ spl12_86 ),
    inference(avatar_split_clause,[],[f490,f487,f495])).

fof(f495,plain,
    ( spl12_88
  <=> l1_struct_0(sK4(sK4(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_88])])).

fof(f487,plain,
    ( spl12_86
  <=> l1_orders_2(sK4(sK4(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).

fof(f490,plain,
    ( l1_struct_0(sK4(sK4(sK11)))
    | ~ spl12_86 ),
    inference(unit_resulting_resolution,[],[f488,f95])).

fof(f488,plain,
    ( l1_orders_2(sK4(sK4(sK11)))
    | ~ spl12_86 ),
    inference(avatar_component_clause,[],[f487])).

fof(f489,plain,
    ( spl12_86
    | ~ spl12_58
    | ~ spl12_82 ),
    inference(avatar_split_clause,[],[f474,f471,f356,f487])).

fof(f356,plain,
    ( spl12_58
  <=> l1_struct_0(sK4(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f471,plain,
    ( spl12_82
  <=> l1_waybel_0(sK4(sK4(sK11)),sK4(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_82])])).

fof(f474,plain,
    ( l1_orders_2(sK4(sK4(sK11)))
    | ~ spl12_58
    | ~ spl12_82 ),
    inference(unit_resulting_resolution,[],[f357,f472,f98])).

fof(f472,plain,
    ( l1_waybel_0(sK4(sK4(sK11)),sK4(sK11))
    | ~ spl12_82 ),
    inference(avatar_component_clause,[],[f471])).

fof(f357,plain,
    ( l1_struct_0(sK4(sK11))
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f356])).

fof(f482,plain,
    ( spl12_84
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f475,f234,f203,f196,f161,f154,f147,f126,f480])).

fof(f475,plain,
    ( v4_orders_2(sK2)
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f204,f111])).

fof(f473,plain,
    ( spl12_82
    | ~ spl12_58 ),
    inference(avatar_split_clause,[],[f361,f356,f471])).

fof(f361,plain,
    ( l1_waybel_0(sK4(sK4(sK11)),sK4(sK11))
    | ~ spl12_58 ),
    inference(unit_resulting_resolution,[],[f357,f99])).

fof(f465,plain,
    ( ~ spl12_81
    | spl12_1
    | spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f458,f234,f203,f196,f161,f154,f147,f126,f463])).

fof(f458,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f127,f235,f148,f155,f162,f197,f204,f110])).

fof(f457,plain,
    ( spl12_78
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f403,f210,f140,f133,f126,f455])).

fof(f403,plain,
    ( m1_connsp_2(sK7(sK0,sK3),sK0,sK3)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24 ),
    inference(unit_resulting_resolution,[],[f127,f134,f141,f211,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f50,f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_m1_connsp_2)).

fof(f449,plain,
    ( spl12_76
    | ~ spl12_74 ),
    inference(avatar_split_clause,[],[f442,f439,f447])).

fof(f447,plain,
    ( spl12_76
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_76])])).

fof(f439,plain,
    ( spl12_74
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_74])])).

fof(f442,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl12_74 ),
    inference(superposition,[],[f104,f440])).

fof(f440,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl12_74 ),
    inference(avatar_component_clause,[],[f439])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_m1_subset_1)).

fof(f441,plain,
    ( spl12_74
    | ~ spl12_12
    | ~ spl12_72 ),
    inference(avatar_split_clause,[],[f426,f418,f168,f439])).

fof(f168,plain,
    ( spl12_12
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f418,plain,
    ( spl12_72
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).

fof(f426,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl12_12
    | ~ spl12_72 ),
    inference(unit_resulting_resolution,[],[f419,f253])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl12_12 ),
    inference(backward_demodulation,[],[f251,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',t6_boole)).

fof(f251,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f169,f97])).

fof(f169,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f419,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl12_72 ),
    inference(avatar_component_clause,[],[f418])).

fof(f420,plain,
    ( spl12_72
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f413,f168,f418])).

fof(f413,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f104,f362,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',t2_subset)).

fof(f362,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f169,f104,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',t5_subset)).

fof(f411,plain,
    ( spl12_70
    | ~ spl12_68 ),
    inference(avatar_split_clause,[],[f402,f399,f409])).

fof(f409,plain,
    ( spl12_70
  <=> l1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f399,plain,
    ( spl12_68
  <=> l1_orders_2(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f402,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl12_68 ),
    inference(unit_resulting_resolution,[],[f400,f95])).

fof(f400,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f399])).

fof(f401,plain,
    ( spl12_68
    | ~ spl12_48
    | ~ spl12_66 ),
    inference(avatar_split_clause,[],[f394,f391,f313,f399])).

fof(f313,plain,
    ( spl12_48
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f391,plain,
    ( spl12_66
  <=> l1_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_66])])).

fof(f394,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl12_48
    | ~ spl12_66 ),
    inference(unit_resulting_resolution,[],[f314,f392,f98])).

fof(f392,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl12_66 ),
    inference(avatar_component_clause,[],[f391])).

fof(f314,plain,
    ( l1_struct_0(sK1)
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f313])).

fof(f393,plain,
    ( spl12_66
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f316,f313,f391])).

fof(f316,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl12_48 ),
    inference(unit_resulting_resolution,[],[f314,f99])).

fof(f384,plain,
    ( spl12_64
    | ~ spl12_56 ),
    inference(avatar_split_clause,[],[f360,f349,f382])).

fof(f382,plain,
    ( spl12_64
  <=> l1_struct_0(sK4(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f349,plain,
    ( spl12_56
  <=> l1_orders_2(sK4(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f360,plain,
    ( l1_struct_0(sK4(sK10))
    | ~ spl12_56 ),
    inference(unit_resulting_resolution,[],[f350,f95])).

fof(f350,plain,
    ( l1_orders_2(sK4(sK10))
    | ~ spl12_56 ),
    inference(avatar_component_clause,[],[f349])).

fof(f377,plain,
    ( spl12_62
    | ~ spl12_54 ),
    inference(avatar_split_clause,[],[f359,f339,f375])).

fof(f375,plain,
    ( spl12_62
  <=> l1_struct_0(sK4(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f339,plain,
    ( spl12_54
  <=> l1_orders_2(sK4(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f359,plain,
    ( l1_struct_0(sK4(sK9))
    | ~ spl12_54 ),
    inference(unit_resulting_resolution,[],[f340,f95])).

fof(f340,plain,
    ( l1_orders_2(sK4(sK9))
    | ~ spl12_54 ),
    inference(avatar_component_clause,[],[f339])).

fof(f369,plain,
    ( spl12_60
    | ~ spl12_52 ),
    inference(avatar_split_clause,[],[f334,f331,f367])).

fof(f331,plain,
    ( spl12_52
  <=> l1_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).

fof(f334,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl12_52 ),
    inference(unit_resulting_resolution,[],[f332,f95])).

fof(f332,plain,
    ( l1_orders_2(sK4(sK0))
    | ~ spl12_52 ),
    inference(avatar_component_clause,[],[f331])).

fof(f358,plain,
    ( spl12_58
    | ~ spl12_50 ),
    inference(avatar_split_clause,[],[f326,f323,f356])).

fof(f323,plain,
    ( spl12_50
  <=> l1_orders_2(sK4(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f326,plain,
    ( l1_struct_0(sK4(sK11))
    | ~ spl12_50 ),
    inference(unit_resulting_resolution,[],[f324,f95])).

fof(f324,plain,
    ( l1_orders_2(sK4(sK11))
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f323])).

fof(f351,plain,
    ( spl12_56
    | ~ spl12_34
    | ~ spl12_44 ),
    inference(avatar_split_clause,[],[f299,f293,f248,f349])).

fof(f248,plain,
    ( spl12_34
  <=> l1_struct_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f293,plain,
    ( spl12_44
  <=> l1_waybel_0(sK4(sK10),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f299,plain,
    ( l1_orders_2(sK4(sK10))
    | ~ spl12_34
    | ~ spl12_44 ),
    inference(unit_resulting_resolution,[],[f249,f294,f98])).

fof(f294,plain,
    ( l1_waybel_0(sK4(sK10),sK10)
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f293])).

fof(f249,plain,
    ( l1_struct_0(sK10)
    | ~ spl12_34 ),
    inference(avatar_component_clause,[],[f248])).

fof(f341,plain,
    ( spl12_54
    | ~ spl12_32
    | ~ spl12_42 ),
    inference(avatar_split_clause,[],[f298,f286,f241,f339])).

fof(f241,plain,
    ( spl12_32
  <=> l1_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f286,plain,
    ( spl12_42
  <=> l1_waybel_0(sK4(sK9),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f298,plain,
    ( l1_orders_2(sK4(sK9))
    | ~ spl12_32
    | ~ spl12_42 ),
    inference(unit_resulting_resolution,[],[f242,f287,f98])).

fof(f287,plain,
    ( l1_waybel_0(sK4(sK9),sK9)
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f286])).

fof(f242,plain,
    ( l1_struct_0(sK9)
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f241])).

fof(f333,plain,
    ( spl12_52
    | ~ spl12_30
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f297,f279,f234,f331])).

fof(f279,plain,
    ( spl12_40
  <=> l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).

fof(f297,plain,
    ( l1_orders_2(sK4(sK0))
    | ~ spl12_30
    | ~ spl12_40 ),
    inference(unit_resulting_resolution,[],[f235,f280,f98])).

fof(f280,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl12_40 ),
    inference(avatar_component_clause,[],[f279])).

fof(f325,plain,
    ( spl12_50
    | ~ spl12_18
    | ~ spl12_38 ),
    inference(avatar_split_clause,[],[f300,f272,f189,f323])).

fof(f189,plain,
    ( spl12_18
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f272,plain,
    ( spl12_38
  <=> l1_waybel_0(sK4(sK11),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f300,plain,
    ( l1_orders_2(sK4(sK11))
    | ~ spl12_18
    | ~ spl12_38 ),
    inference(unit_resulting_resolution,[],[f190,f273,f98])).

fof(f273,plain,
    ( l1_waybel_0(sK4(sK11),sK11)
    | ~ spl12_38 ),
    inference(avatar_component_clause,[],[f272])).

fof(f190,plain,
    ( l1_struct_0(sK11)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f315,plain,
    ( spl12_48
    | ~ spl12_46 ),
    inference(avatar_split_clause,[],[f308,f305,f313])).

fof(f305,plain,
    ( spl12_46
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).

fof(f308,plain,
    ( l1_struct_0(sK1)
    | ~ spl12_46 ),
    inference(unit_resulting_resolution,[],[f306,f95])).

fof(f306,plain,
    ( l1_orders_2(sK1)
    | ~ spl12_46 ),
    inference(avatar_component_clause,[],[f305])).

fof(f307,plain,
    ( spl12_46
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f296,f234,f196,f305])).

fof(f296,plain,
    ( l1_orders_2(sK1)
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f235,f197,f98])).

fof(f295,plain,
    ( spl12_44
    | ~ spl12_34 ),
    inference(avatar_split_clause,[],[f266,f248,f293])).

fof(f266,plain,
    ( l1_waybel_0(sK4(sK10),sK10)
    | ~ spl12_34 ),
    inference(unit_resulting_resolution,[],[f249,f99])).

fof(f288,plain,
    ( spl12_42
    | ~ spl12_32 ),
    inference(avatar_split_clause,[],[f265,f241,f286])).

fof(f265,plain,
    ( l1_waybel_0(sK4(sK9),sK9)
    | ~ spl12_32 ),
    inference(unit_resulting_resolution,[],[f242,f99])).

fof(f281,plain,
    ( spl12_40
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f264,f234,f279])).

fof(f264,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f235,f99])).

fof(f274,plain,
    ( spl12_38
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f267,f189,f272])).

fof(f267,plain,
    ( l1_waybel_0(sK4(sK11),sK11)
    | ~ spl12_18 ),
    inference(unit_resulting_resolution,[],[f190,f99])).

fof(f260,plain,
    ( spl12_36
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f251,f168,f258])).

fof(f258,plain,
    ( spl12_36
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f250,plain,
    ( spl12_34
    | ~ spl12_16 ),
    inference(avatar_split_clause,[],[f229,f182,f248])).

fof(f182,plain,
    ( spl12_16
  <=> l1_pre_topc(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f229,plain,
    ( l1_struct_0(sK10)
    | ~ spl12_16 ),
    inference(unit_resulting_resolution,[],[f183,f96])).

fof(f96,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',dt_l1_pre_topc)).

fof(f183,plain,
    ( l1_pre_topc(sK10)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f243,plain,
    ( spl12_32
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f227,f175,f241])).

fof(f175,plain,
    ( spl12_14
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f227,plain,
    ( l1_struct_0(sK9)
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f176,f95])).

fof(f176,plain,
    ( l1_orders_2(sK9)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f236,plain,
    ( spl12_30
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f228,f140,f234])).

fof(f228,plain,
    ( l1_struct_0(sK0)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f141,f96])).

fof(f226,plain,(
    ~ spl12_29 ),
    inference(avatar_split_clause,[],[f93,f224])).

fof(f93,plain,(
    ~ r3_waybel_9(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ r3_waybel_9(sK0,sK1,sK3)
    & r3_waybel_9(sK0,sK2,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m2_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f63,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_waybel_9(X0,X1,X3)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(sK0,X1,X3)
                  & r3_waybel_9(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m2_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_waybel_9(X0,sK1,X3)
                & r3_waybel_9(X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m2_yellow_6(X2,X0,sK1) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_waybel_9(X0,X1,X3)
              & r3_waybel_9(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m2_yellow_6(X2,X0,X1) )
     => ( ? [X3] :
            ( ~ r3_waybel_9(X0,X1,X3)
            & r3_waybel_9(X0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m2_yellow_6(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_waybel_9(X0,X1,X3)
          & r3_waybel_9(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_waybel_9(X0,X1,sK3)
        & r3_waybel_9(X0,X2,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
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
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
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
                ( m2_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_waybel_9(X0,X2,X3)
                     => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',t31_waybel_9)).

fof(f219,plain,(
    spl12_26 ),
    inference(avatar_split_clause,[],[f92,f217])).

fof(f92,plain,(
    r3_waybel_9(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f212,plain,(
    spl12_24 ),
    inference(avatar_split_clause,[],[f91,f210])).

fof(f91,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f205,plain,(
    spl12_22 ),
    inference(avatar_split_clause,[],[f90,f203])).

fof(f90,plain,(
    m2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f198,plain,(
    spl12_20 ),
    inference(avatar_split_clause,[],[f89,f196])).

fof(f89,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f191,plain,(
    spl12_18 ),
    inference(avatar_split_clause,[],[f121,f189])).

fof(f121,plain,(
    l1_struct_0(sK11) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    l1_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f18,f81])).

fof(f81,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK11) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_l1_struct_0)).

fof(f184,plain,(
    spl12_16 ),
    inference(avatar_split_clause,[],[f120,f182])).

fof(f120,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    l1_pre_topc(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f17,f79])).

fof(f79,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK10) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_l1_pre_topc)).

fof(f177,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f119,f175])).

fof(f119,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    l1_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f16,f77])).

fof(f77,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK9) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',existence_l1_orders_2)).

fof(f170,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f94,f168])).

fof(f94,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t31_waybel_9.p',dt_o_0_0_xboole_0)).

fof(f163,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f88,f161])).

fof(f88,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f156,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f87,f154])).

fof(f87,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f149,plain,(
    ~ spl12_7 ),
    inference(avatar_split_clause,[],[f86,f147])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f142,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f85,f140])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f135,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f84,f133])).

fof(f84,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f128,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f83,f126])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
