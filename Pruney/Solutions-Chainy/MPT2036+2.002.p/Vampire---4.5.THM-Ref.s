%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 653 expanded)
%              Number of leaves         :   59 ( 300 expanded)
%              Depth                    :   13
%              Number of atoms          : 1495 (5332 expanded)
%              Number of equality atoms :   66 ( 291 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f584,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f203,f223,f229,f238,f244,f265,f273,f280,f286,f323,f356,f379,f434,f438,f463,f477,f482,f492,f545,f553,f581])).

fof(f581,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_47
    | ~ spl10_48
    | spl10_50
    | ~ spl10_54 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_47
    | ~ spl10_48
    | spl10_50
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f579,f481])).

fof(f481,plain,
    ( r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl10_48
  <=> r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f579,plain,
    ( ~ r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_47
    | spl10_50
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f569,f279])).

fof(f279,plain,
    ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = k2_relat_1(u1_waybel_0(sK4,sK6))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl10_28
  <=> k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = k2_relat_1(u1_waybel_0(sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f569,plain,
    ( ~ r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_47
    | spl10_50
    | ~ spl10_54 ),
    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f127,f157,f491,f476,f552,f116])).

fof(f116,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | r3_orders_2(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
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
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,axiom,(
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

fof(f552,plain,
    ( v5_pre_topc(k4_waybel_1(sK4,sK8(sK4)),sK4,sK4)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl10_54
  <=> v5_pre_topc(k4_waybel_1(sK4,sK8(sK4)),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f476,plain,
    ( m1_subset_1(sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))),u1_struct_0(sK4))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl10_47
  <=> m1_subset_1(sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f491,plain,
    ( ~ r3_orders_2(sK4,sK5,sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | spl10_50 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl10_50
  <=> r3_orders_2(sK4,sK5,sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f157,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl10_8
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f127,plain,
    ( r3_waybel_9(sK4,sK6,sK5)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_2
  <=> r3_waybel_9(sK4,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f137,plain,
    ( l1_waybel_0(sK6,sK4)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl10_4
  <=> l1_waybel_0(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f142,plain,
    ( v7_waybel_0(sK6)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl10_5
  <=> v7_waybel_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f147,plain,
    ( v4_orders_2(sK6)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl10_6
  <=> v4_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f152,plain,
    ( ~ v2_struct_0(sK6)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_7
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f162,plain,
    ( l1_waybel_9(sK4)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_9
  <=> l1_waybel_9(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f167,plain,
    ( v1_compts_1(sK4)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl10_10
  <=> v1_compts_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f172,plain,
    ( v2_lattice3(sK4)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl10_11
  <=> v2_lattice3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f177,plain,
    ( v1_lattice3(sK4)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl10_12
  <=> v1_lattice3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f182,plain,
    ( v5_orders_2(sK4)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl10_13
  <=> v5_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f187,plain,
    ( v4_orders_2(sK4)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl10_14
  <=> v4_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f192,plain,
    ( v3_orders_2(sK4)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl10_15
  <=> v3_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f197,plain,
    ( v8_pre_topc(sK4)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl10_16
  <=> v8_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f202,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl10_17
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f553,plain,
    ( spl10_54
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f546,f535,f550])).

fof(f535,plain,
    ( spl10_52
  <=> m1_subset_1(sK8(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f546,plain,
    ( v5_pre_topc(k4_waybel_1(sK4,sK8(sK4)),sK4,sK4)
    | ~ spl10_52 ),
    inference(unit_resulting_resolution,[],[f537,f78])).

fof(f78,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
      | ~ m1_subset_1(X3,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( sK5 != k1_waybel_2(sK4,sK6)
    & r3_waybel_9(sK4,sK6,sK5)
    & v10_waybel_0(sK6,sK4)
    & ! [X3] :
        ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
    & l1_waybel_0(sK6,sK4)
    & v7_waybel_0(sK6)
    & v4_orders_2(sK6)
    & ~ v2_struct_0(sK6)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_waybel_9(sK4)
    & v1_compts_1(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & v8_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_2(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v10_waybel_0(X2,X0)
                & ! [X3] :
                    ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( ? [X2] :
              ( k1_waybel_2(sK4,X2) != X1
              & r3_waybel_9(sK4,X2,X1)
              & v10_waybel_0(X2,sK4)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
                  | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
              & l1_waybel_0(X2,sK4)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_waybel_9(sK4)
      & v1_compts_1(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & v8_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_waybel_2(sK4,X2) != X1
            & r3_waybel_9(sK4,X2,X1)
            & v10_waybel_0(X2,sK4)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
                | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
            & l1_waybel_0(X2,sK4)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( k1_waybel_2(sK4,X2) != sK5
          & r3_waybel_9(sK4,X2,sK5)
          & v10_waybel_0(X2,sK4)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
              | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
          & l1_waybel_0(X2,sK4)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( k1_waybel_2(sK4,X2) != sK5
        & r3_waybel_9(sK4,X2,sK5)
        & v10_waybel_0(X2,sK4)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
            | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
        & l1_waybel_0(X2,sK4)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( sK5 != k1_waybel_2(sK4,sK6)
      & r3_waybel_9(sK4,sK6,sK5)
      & v10_waybel_0(sK6,sK4)
      & ! [X3] :
          ( v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4)
          | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
      & l1_waybel_0(sK6,sK4)
      & v7_waybel_0(sK6)
      & v4_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f537,plain,
    ( m1_subset_1(sK8(sK4),u1_struct_0(sK4))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f535])).

fof(f545,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_47
    | ~ spl10_48
    | spl10_50
    | spl10_52 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_47
    | ~ spl10_48
    | spl10_50
    | spl10_52 ),
    inference(subsumption_resolution,[],[f543,f481])).

fof(f543,plain,
    ( ~ r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_47
    | spl10_50
    | spl10_52 ),
    inference(forward_demodulation,[],[f542,f279])).

fof(f542,plain,
    ( ~ r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_47
    | spl10_50
    | spl10_52 ),
    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f127,f157,f491,f476,f536,f115])).

fof(f115,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | r3_orders_2(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
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
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
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
    inference(cnf_transformation,[],[f53])).

fof(f536,plain,
    ( ~ m1_subset_1(sK8(sK4),u1_struct_0(sK4))
    | spl10_52 ),
    inference(avatar_component_clause,[],[f535])).

fof(f492,plain,
    ( ~ spl10_50
    | ~ spl10_8
    | ~ spl10_15
    | ~ spl10_20
    | spl10_22
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f469,f376,f233,f219,f190,f155,f489])).

fof(f219,plain,
    ( spl10_20
  <=> l1_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f233,plain,
    ( spl10_22
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f376,plain,
    ( spl10_40
  <=> sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f469,plain,
    ( ~ r3_orders_2(sK4,sK5,sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_8
    | ~ spl10_15
    | ~ spl10_20
    | spl10_22
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f221,f235,f192,f157,f378,f383])).

fof(f383,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,sK9(X1,X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP0(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f382,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X1,X0,sK9(X0,X1,X2))
        & r2_lattice3(X1,X2,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK9(X0,X1,X2))
        & r2_lattice3(X1,X2,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f382,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,sK9(X1,X0,X2))
      | ~ m1_subset_1(sK9(X1,X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP0(X1,X0,X2) ) ),
    inference(resolution,[],[f107,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK9(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f378,plain,
    ( sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f376])).

fof(f235,plain,
    ( ~ v2_struct_0(sK4)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f233])).

fof(f221,plain,
    ( l1_orders_2(sK4)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f482,plain,
    ( spl10_48
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f471,f376,f479])).

fof(f471,plain,
    ( r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f378,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK9(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f477,plain,
    ( spl10_47
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f472,f376,f474])).

fof(f472,plain,
    ( m1_subset_1(sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))),u1_struct_0(sK4))
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f378,f96])).

fof(f463,plain,
    ( spl10_39
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f460,f431,f277,f200,f195,f190,f185,f180,f175,f170,f165,f160,f155,f150,f145,f140,f135,f130,f125,f372])).

fof(f372,plain,
    ( spl10_39
  <=> r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f130,plain,
    ( spl10_3
  <=> v10_waybel_0(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f431,plain,
    ( spl10_43
  <=> v5_pre_topc(k4_waybel_1(sK4,sK7(sK4)),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f460,plain,
    ( r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | ~ spl10_43 ),
    inference(forward_demodulation,[],[f457,f279])).

fof(f457,plain,
    ( r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f132,f127,f157,f433,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
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
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
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
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
                    & m1_subset_1(sK7(X0),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f433,plain,
    ( v5_pre_topc(k4_waybel_1(sK4,sK7(sK4)),sK4,sK4)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f431])).

fof(f132,plain,
    ( v10_waybel_0(sK6,sK4)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f438,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | spl10_39
    | spl10_41 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | spl10_39
    | spl10_41 ),
    inference(subsumption_resolution,[],[f436,f374])).

fof(f374,plain,
    ( ~ r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5)
    | spl10_39 ),
    inference(avatar_component_clause,[],[f372])).

fof(f436,plain,
    ( r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_28
    | spl10_41 ),
    inference(forward_demodulation,[],[f435,f279])).

fof(f435,plain,
    ( r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | spl10_41 ),
    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f132,f127,f157,f421,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
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
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
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
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f50])).

fof(f421,plain,
    ( ~ m1_subset_1(sK7(sK4),u1_struct_0(sK4))
    | spl10_41 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl10_41
  <=> m1_subset_1(sK7(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f434,plain,
    ( spl10_43
    | ~ spl10_41 ),
    inference(avatar_split_clause,[],[f427,f420,f431])).

fof(f427,plain,
    ( v5_pre_topc(k4_waybel_1(sK4,sK7(sK4)),sK4,sK4)
    | ~ spl10_41 ),
    inference(unit_resulting_resolution,[],[f422,f78])).

fof(f422,plain,
    ( m1_subset_1(sK7(sK4),u1_struct_0(sK4))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f420])).

fof(f379,plain,
    ( ~ spl10_39
    | spl10_40
    | spl10_1
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f370,f353,f219,f180,f155,f120,f376,f372])).

fof(f120,plain,
    ( spl10_1
  <=> sK5 = k1_waybel_2(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f353,plain,
    ( spl10_38
  <=> k1_waybel_2(sK4,sK6) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f370,plain,
    ( sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5)
    | spl10_1
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f368,f122])).

fof(f122,plain,
    ( sK5 != k1_waybel_2(sK4,sK6)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f368,plain,
    ( sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5)
    | sK5 = k1_waybel_2(sK4,sK6)
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_38 ),
    inference(resolution,[],[f364,f258])).

fof(f258,plain,
    ( ! [X0] : sP2(X0,sK4,sK5)
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f182,f221,f157,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X2,X0,X1)
              & sP1(X1,X0,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f32,f41,f40,f39])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( ! [X4] :
            ( r1_orders_2(X0,X1,X4)
            | ~ r2_lattice3(X0,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_lattice3(X0,X2,X1) )
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ( r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | sP0(X1,X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f364,plain,
    ( ! [X0] :
        ( ~ sP2(k2_relat_1(u1_waybel_0(sK4,sK6)),sK4,X0)
        | sP0(X0,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
        | ~ r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),X0)
        | k1_waybel_2(sK4,sK6) = X0 )
    | ~ spl10_38 ),
    inference(superposition,[],[f355,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X1,X0) = X2
      | sP0(X2,X1,X0)
      | ~ r2_lattice3(X1,X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r1_yellow_0(X1,X0)
        & k1_yellow_0(X1,X0) = X2 )
      | sP0(X2,X1,X0)
      | ~ r2_lattice3(X1,X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ( r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | sP0(X1,X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f355,plain,
    ( k1_waybel_2(sK4,sK6) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f353])).

fof(f356,plain,
    ( spl10_38
    | ~ spl10_29
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f351,f320,f283,f353])).

fof(f283,plain,
    ( spl10_29
  <=> k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f320,plain,
    ( spl10_34
  <=> k1_waybel_2(sK4,sK6) = k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f351,plain,
    ( k1_waybel_2(sK4,sK6) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ spl10_29
    | ~ spl10_34 ),
    inference(backward_demodulation,[],[f285,f322])).

fof(f322,plain,
    ( k1_waybel_2(sK4,sK6) = k4_yellow_2(sK4,u1_waybel_0(sK4,sK6))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f320])).

fof(f285,plain,
    ( k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f283])).

fof(f323,plain,
    ( spl10_34
    | ~ spl10_4
    | ~ spl10_20
    | spl10_22 ),
    inference(avatar_split_clause,[],[f315,f233,f219,f135,f320])).

fof(f315,plain,
    ( k1_waybel_2(sK4,sK6) = k4_yellow_2(sK4,u1_waybel_0(sK4,sK6))
    | ~ spl10_4
    | ~ spl10_20
    | spl10_22 ),
    inference(unit_resulting_resolution,[],[f235,f221,f137,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_2)).

fof(f286,plain,
    ( spl10_29
    | ~ spl10_20
    | spl10_22
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f281,f269,f233,f219,f283])).

fof(f269,plain,
    ( spl10_27
  <=> v1_relat_1(u1_waybel_0(sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f281,plain,
    ( k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))
    | ~ spl10_20
    | spl10_22
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f235,f221,f271,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_2)).

fof(f271,plain,
    ( v1_relat_1(u1_waybel_0(sK4,sK6))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f269])).

fof(f280,plain,
    ( spl10_28
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f275,f262,f277])).

fof(f262,plain,
    ( spl10_26
  <=> m1_subset_1(u1_waybel_0(sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f275,plain,
    ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = k2_relat_1(u1_waybel_0(sK4,sK6))
    | ~ spl10_26 ),
    inference(unit_resulting_resolution,[],[f264,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f264,plain,
    ( m1_subset_1(u1_waybel_0(sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f262])).

fof(f273,plain,
    ( spl10_27
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f267,f262,f269])).

fof(f267,plain,
    ( v1_relat_1(u1_waybel_0(sK4,sK6))
    | ~ spl10_26 ),
    inference(resolution,[],[f264,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f265,plain,
    ( spl10_26
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f259,f241,f262])).

fof(f241,plain,
    ( spl10_23
  <=> sP3(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f259,plain,
    ( m1_subset_1(u1_waybel_0(sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ spl10_23 ),
    inference(unit_resulting_resolution,[],[f243,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f243,plain,
    ( sP3(sK4,sK6)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f241])).

fof(f244,plain,
    ( spl10_23
    | ~ spl10_4
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f239,f226,f135,f241])).

fof(f226,plain,
    ( spl10_21
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f239,plain,
    ( sP3(sK4,sK6)
    | ~ spl10_4
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f228,f137,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f34,f43])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f228,plain,
    ( l1_struct_0(sK4)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f226])).

fof(f238,plain,
    ( ~ spl10_22
    | ~ spl10_12
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f237,f219,f175,f233])).

fof(f237,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl10_12
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f231,f221])).

fof(f231,plain,
    ( ~ v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl10_12 ),
    inference(resolution,[],[f85,f177])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f229,plain,
    ( spl10_21
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f224,f219,f226])).

fof(f224,plain,
    ( l1_struct_0(sK4)
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f221,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f223,plain,
    ( spl10_20
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f217,f160,f219])).

fof(f217,plain,
    ( l1_orders_2(sK4)
    | ~ spl10_9 ),
    inference(resolution,[],[f83,f162])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f203,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f64,f200])).

fof(f64,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f198,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f65,f195])).

fof(f65,plain,(
    v8_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f193,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f66,f190])).

fof(f66,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f188,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f67,f185])).

fof(f67,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f183,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f68,f180])).

fof(f68,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f178,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f69,f175])).

fof(f69,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f173,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f70,f170])).

fof(f70,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f168,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f71,f165])).

fof(f71,plain,(
    v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f163,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f72,f160])).

fof(f72,plain,(
    l1_waybel_9(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f158,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f73,f155])).

fof(f73,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f153,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f74,f150])).

fof(f74,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f148,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f75,f145])).

fof(f75,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f143,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f76,f140])).

fof(f76,plain,(
    v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f138,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f77,f135])).

fof(f77,plain,(
    l1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f133,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f79,f130])).

fof(f79,plain,(
    v10_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f128,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f80,f125])).

fof(f80,plain,(
    r3_waybel_9(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f123,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f81,f120])).

fof(f81,plain,(
    sK5 != k1_waybel_2(sK4,sK6) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (28092)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (28104)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (28102)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (28104)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f584,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f203,f223,f229,f238,f244,f265,f273,f280,f286,f323,f356,f379,f434,f438,f463,f477,f482,f492,f545,f553,f581])).
% 0.20/0.49  fof(f581,plain,(
% 0.20/0.49    ~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_47 | ~spl10_48 | spl10_50 | ~spl10_54),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f580])).
% 0.20/0.49  fof(f580,plain,(
% 0.20/0.49    $false | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_47 | ~spl10_48 | spl10_50 | ~spl10_54)),
% 0.20/0.49    inference(subsumption_resolution,[],[f579,f481])).
% 0.20/0.49  fof(f481,plain,(
% 0.20/0.49    r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | ~spl10_48),
% 0.20/0.49    inference(avatar_component_clause,[],[f479])).
% 0.20/0.49  fof(f479,plain,(
% 0.20/0.49    spl10_48 <=> r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.20/0.49  fof(f579,plain,(
% 0.20/0.49    ~r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_47 | spl10_50 | ~spl10_54)),
% 0.20/0.49    inference(forward_demodulation,[],[f569,f279])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = k2_relat_1(u1_waybel_0(sK4,sK6)) | ~spl10_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f277])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    spl10_28 <=> k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = k2_relat_1(u1_waybel_0(sK4,sK6))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.20/0.49  fof(f569,plain,(
% 0.20/0.49    ~r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_47 | spl10_50 | ~spl10_54)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f127,f157,f491,f476,f552,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | r3_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.20/0.49    inference(rectify,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).
% 0.20/0.49  fof(f552,plain,(
% 0.20/0.49    v5_pre_topc(k4_waybel_1(sK4,sK8(sK4)),sK4,sK4) | ~spl10_54),
% 0.20/0.49    inference(avatar_component_clause,[],[f550])).
% 0.20/0.49  fof(f550,plain,(
% 0.20/0.49    spl10_54 <=> v5_pre_topc(k4_waybel_1(sK4,sK8(sK4)),sK4,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).
% 0.20/0.49  fof(f476,plain,(
% 0.20/0.49    m1_subset_1(sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))),u1_struct_0(sK4)) | ~spl10_47),
% 0.20/0.49    inference(avatar_component_clause,[],[f474])).
% 0.20/0.49  fof(f474,plain,(
% 0.20/0.49    spl10_47 <=> m1_subset_1(sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))),u1_struct_0(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    ~r3_orders_2(sK4,sK5,sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | spl10_50),
% 0.20/0.49    inference(avatar_component_clause,[],[f489])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    spl10_50 <=> r3_orders_2(sK4,sK5,sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK4)) | ~spl10_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f155])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl10_8 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    r3_waybel_9(sK4,sK6,sK5) | ~spl10_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl10_2 <=> r3_waybel_9(sK4,sK6,sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    l1_waybel_0(sK6,sK4) | ~spl10_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl10_4 <=> l1_waybel_0(sK6,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    v7_waybel_0(sK6) | ~spl10_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl10_5 <=> v7_waybel_0(sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    v4_orders_2(sK6) | ~spl10_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    spl10_6 <=> v4_orders_2(sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ~v2_struct_0(sK6) | spl10_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl10_7 <=> v2_struct_0(sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    l1_waybel_9(sK4) | ~spl10_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f160])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl10_9 <=> l1_waybel_9(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    v1_compts_1(sK4) | ~spl10_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f165])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl10_10 <=> v1_compts_1(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    v2_lattice3(sK4) | ~spl10_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    spl10_11 <=> v2_lattice3(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    v1_lattice3(sK4) | ~spl10_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f175])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    spl10_12 <=> v1_lattice3(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    v5_orders_2(sK4) | ~spl10_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl10_13 <=> v5_orders_2(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    v4_orders_2(sK4) | ~spl10_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl10_14 <=> v4_orders_2(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    v3_orders_2(sK4) | ~spl10_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl10_15 <=> v3_orders_2(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    v8_pre_topc(sK4) | ~spl10_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl10_16 <=> v8_pre_topc(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    v2_pre_topc(sK4) | ~spl10_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f200])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    spl10_17 <=> v2_pre_topc(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.49  fof(f553,plain,(
% 0.20/0.49    spl10_54 | ~spl10_52),
% 0.20/0.49    inference(avatar_split_clause,[],[f546,f535,f550])).
% 0.20/0.49  fof(f535,plain,(
% 0.20/0.49    spl10_52 <=> m1_subset_1(sK8(sK4),u1_struct_0(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 0.20/0.49  fof(f546,plain,(
% 0.20/0.49    v5_pre_topc(k4_waybel_1(sK4,sK8(sK4)),sK4,sK4) | ~spl10_52),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f537,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ((sK5 != k1_waybel_2(sK4,sK6) & r3_waybel_9(sK4,sK6,sK5) & v10_waybel_0(sK6,sK4) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) & l1_waybel_0(sK6,sK4) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_waybel_9(sK4) & v1_compts_1(sK4) & v2_lattice3(sK4) & v1_lattice3(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & v8_pre_topc(sK4) & v2_pre_topc(sK4)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f47,f46,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_2(sK4,X2) != X1 & r3_waybel_9(sK4,X2,X1) & v10_waybel_0(X2,sK4) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) & l1_waybel_0(X2,sK4) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_waybel_9(sK4) & v1_compts_1(sK4) & v2_lattice3(sK4) & v1_lattice3(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & v8_pre_topc(sK4) & v2_pre_topc(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (k1_waybel_2(sK4,X2) != X1 & r3_waybel_9(sK4,X2,X1) & v10_waybel_0(X2,sK4) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) & l1_waybel_0(X2,sK4) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK4))) => (? [X2] : (k1_waybel_2(sK4,X2) != sK5 & r3_waybel_9(sK4,X2,sK5) & v10_waybel_0(X2,sK4) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) & l1_waybel_0(X2,sK4) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ? [X2] : (k1_waybel_2(sK4,X2) != sK5 & r3_waybel_9(sK4,X2,sK5) & v10_waybel_0(X2,sK4) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) & l1_waybel_0(X2,sK4) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (sK5 != k1_waybel_2(sK4,sK6) & r3_waybel_9(sK4,sK6,sK5) & v10_waybel_0(sK6,sK4) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK4,X3),sK4,sK4) | ~m1_subset_1(X3,u1_struct_0(sK4))) & l1_waybel_0(sK6,sK4) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).
% 0.20/0.49  fof(f537,plain,(
% 0.20/0.49    m1_subset_1(sK8(sK4),u1_struct_0(sK4)) | ~spl10_52),
% 0.20/0.49    inference(avatar_component_clause,[],[f535])).
% 0.20/0.49  fof(f545,plain,(
% 0.20/0.49    ~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_47 | ~spl10_48 | spl10_50 | spl10_52),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f544])).
% 0.20/0.49  fof(f544,plain,(
% 0.20/0.49    $false | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_47 | ~spl10_48 | spl10_50 | spl10_52)),
% 0.20/0.49    inference(subsumption_resolution,[],[f543,f481])).
% 0.20/0.49  fof(f543,plain,(
% 0.20/0.49    ~r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_47 | spl10_50 | spl10_52)),
% 0.20/0.49    inference(forward_demodulation,[],[f542,f279])).
% 0.20/0.49  fof(f542,plain,(
% 0.20/0.49    ~r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_47 | spl10_50 | spl10_52)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f127,f157,f491,f476,f536,f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | r3_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f53])).
% 0.20/0.49  fof(f536,plain,(
% 0.20/0.49    ~m1_subset_1(sK8(sK4),u1_struct_0(sK4)) | spl10_52),
% 0.20/0.49    inference(avatar_component_clause,[],[f535])).
% 0.20/0.49  fof(f492,plain,(
% 0.20/0.49    ~spl10_50 | ~spl10_8 | ~spl10_15 | ~spl10_20 | spl10_22 | ~spl10_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f469,f376,f233,f219,f190,f155,f489])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    spl10_20 <=> l1_orders_2(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    spl10_22 <=> v2_struct_0(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    spl10_40 <=> sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.20/0.49  fof(f469,plain,(
% 0.20/0.49    ~r3_orders_2(sK4,sK5,sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | (~spl10_8 | ~spl10_15 | ~spl10_20 | spl10_22 | ~spl10_40)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f221,f235,f192,f157,f378,f383])).
% 0.20/0.49  fof(f383,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,sK9(X1,X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~sP0(X1,X0,X2)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f382,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((~r1_orders_2(X1,X0,sK9(X0,X1,X2)) & r2_lattice3(X1,X2,sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) | ~sP0(X0,X1,X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f59,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK9(X0,X1,X2)) & r2_lattice3(X1,X2,sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X0,X1,X2))),
% 0.20/0.49    inference(rectify,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ! [X1,X0,X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X1,X0,X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f382,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,sK9(X1,X0,X2)) | ~m1_subset_1(sK9(X1,X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~sP0(X1,X0,X2)) )),
% 0.20/0.49    inference(resolution,[],[f107,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,sK9(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f61])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.49  fof(f378,plain,(
% 0.20/0.49    sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | ~spl10_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f376])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    ~v2_struct_0(sK4) | spl10_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f233])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    l1_orders_2(sK4) | ~spl10_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f219])).
% 0.20/0.49  fof(f482,plain,(
% 0.20/0.49    spl10_48 | ~spl10_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f471,f376,f479])).
% 0.20/0.49  fof(f471,plain,(
% 0.20/0.49    r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))) | ~spl10_40),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f378,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_lattice3(X1,X2,sK9(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f61])).
% 0.20/0.49  fof(f477,plain,(
% 0.20/0.49    spl10_47 | ~spl10_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f472,f376,f474])).
% 0.20/0.49  fof(f472,plain,(
% 0.20/0.49    m1_subset_1(sK9(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))),u1_struct_0(sK4)) | ~spl10_40),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f378,f96])).
% 0.20/0.49  fof(f463,plain,(
% 0.20/0.49    spl10_39 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_43),
% 0.20/0.49    inference(avatar_split_clause,[],[f460,f431,f277,f200,f195,f190,f185,f180,f175,f170,f165,f160,f155,f150,f145,f140,f135,f130,f125,f372])).
% 0.20/0.49  fof(f372,plain,(
% 0.20/0.49    spl10_39 <=> r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl10_3 <=> v10_waybel_0(sK6,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.49  fof(f431,plain,(
% 0.20/0.49    spl10_43 <=> v5_pre_topc(k4_waybel_1(sK4,sK7(sK4)),sK4,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 0.20/0.49  fof(f460,plain,(
% 0.20/0.49    r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | ~spl10_43)),
% 0.20/0.49    inference(forward_demodulation,[],[f457,f279])).
% 0.20/0.49  fof(f457,plain,(
% 0.20/0.49    r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK5) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_43)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f132,f127,f157,f433,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).
% 0.20/0.49  fof(f433,plain,(
% 0.20/0.49    v5_pre_topc(k4_waybel_1(sK4,sK7(sK4)),sK4,sK4) | ~spl10_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f431])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    v10_waybel_0(sK6,sK4) | ~spl10_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f130])).
% 0.20/0.49  fof(f438,plain,(
% 0.20/0.49    ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | spl10_39 | spl10_41),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f437])).
% 0.20/0.49  fof(f437,plain,(
% 0.20/0.49    $false | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | spl10_39 | spl10_41)),
% 0.20/0.49    inference(subsumption_resolution,[],[f436,f374])).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    ~r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5) | spl10_39),
% 0.20/0.49    inference(avatar_component_clause,[],[f372])).
% 0.20/0.49  fof(f436,plain,(
% 0.20/0.49    r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_28 | spl10_41)),
% 0.20/0.49    inference(forward_demodulation,[],[f435,f279])).
% 0.20/0.49  fof(f435,plain,(
% 0.20/0.49    r2_lattice3(sK4,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)),sK5) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | spl10_41)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f202,f197,f192,f187,f182,f177,f172,f167,f162,f152,f147,f142,f137,f132,f127,f157,f421,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f421,plain,(
% 0.20/0.49    ~m1_subset_1(sK7(sK4),u1_struct_0(sK4)) | spl10_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f420])).
% 0.20/0.49  fof(f420,plain,(
% 0.20/0.49    spl10_41 <=> m1_subset_1(sK7(sK4),u1_struct_0(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.20/0.49  fof(f434,plain,(
% 0.20/0.49    spl10_43 | ~spl10_41),
% 0.20/0.49    inference(avatar_split_clause,[],[f427,f420,f431])).
% 0.20/0.49  fof(f427,plain,(
% 0.20/0.49    v5_pre_topc(k4_waybel_1(sK4,sK7(sK4)),sK4,sK4) | ~spl10_41),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f422,f78])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    m1_subset_1(sK7(sK4),u1_struct_0(sK4)) | ~spl10_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f420])).
% 0.20/0.49  fof(f379,plain,(
% 0.20/0.49    ~spl10_39 | spl10_40 | spl10_1 | ~spl10_8 | ~spl10_13 | ~spl10_20 | ~spl10_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f370,f353,f219,f180,f155,f120,f376,f372])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl10_1 <=> sK5 = k1_waybel_2(sK4,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    spl10_38 <=> k1_waybel_2(sK4,sK6) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | ~r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5) | (spl10_1 | ~spl10_8 | ~spl10_13 | ~spl10_20 | ~spl10_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f368,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    sK5 != k1_waybel_2(sK4,sK6) | spl10_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f120])).
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    sP0(sK5,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | ~r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),sK5) | sK5 = k1_waybel_2(sK4,sK6) | (~spl10_8 | ~spl10_13 | ~spl10_20 | ~spl10_38)),
% 0.20/0.49    inference(resolution,[],[f364,f258])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    ( ! [X0] : (sP2(X0,sK4,sK5)) ) | (~spl10_8 | ~spl10_13 | ~spl10_20)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f182,f221,f157,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (sP2(X2,X0,X1) & sP1(X1,X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(definition_folding,[],[f32,f41,f40,f39])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X1,X0,X2] : ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1 | ~sP1(X1,X0,X2))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X2,X0,X1] : ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | sP0(X1,X0,X2) | ~r2_lattice3(X0,X2,X1) | ~sP2(X2,X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.49    inference(rectify,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.20/0.49  fof(f364,plain,(
% 0.20/0.49    ( ! [X0] : (~sP2(k2_relat_1(u1_waybel_0(sK4,sK6)),sK4,X0) | sP0(X0,sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | ~r2_lattice3(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)),X0) | k1_waybel_2(sK4,sK6) = X0) ) | ~spl10_38),
% 0.20/0.49    inference(superposition,[],[f355,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_yellow_0(X1,X0) = X2 | sP0(X2,X1,X0) | ~r2_lattice3(X1,X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_yellow_0(X1,X0) & k1_yellow_0(X1,X0) = X2) | sP0(X2,X1,X0) | ~r2_lattice3(X1,X0,X2) | ~sP2(X0,X1,X2))),
% 0.20/0.49    inference(rectify,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ! [X2,X0,X1] : ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | sP0(X1,X0,X2) | ~r2_lattice3(X0,X2,X1) | ~sP2(X2,X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f41])).
% 0.20/0.49  fof(f355,plain,(
% 0.20/0.49    k1_waybel_2(sK4,sK6) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | ~spl10_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f353])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    spl10_38 | ~spl10_29 | ~spl10_34),
% 0.20/0.49    inference(avatar_split_clause,[],[f351,f320,f283,f353])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    spl10_29 <=> k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    spl10_34 <=> k1_waybel_2(sK4,sK6) = k4_yellow_2(sK4,u1_waybel_0(sK4,sK6))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    k1_waybel_2(sK4,sK6) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | (~spl10_29 | ~spl10_34)),
% 0.20/0.49    inference(backward_demodulation,[],[f285,f322])).
% 0.20/0.49  fof(f322,plain,(
% 0.20/0.49    k1_waybel_2(sK4,sK6) = k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) | ~spl10_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f320])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | ~spl10_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f283])).
% 0.20/0.49  fof(f323,plain,(
% 0.20/0.49    spl10_34 | ~spl10_4 | ~spl10_20 | spl10_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f315,f233,f219,f135,f320])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    k1_waybel_2(sK4,sK6) = k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) | (~spl10_4 | ~spl10_20 | spl10_22)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f235,f221,f137,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_2)).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    spl10_29 | ~spl10_20 | spl10_22 | ~spl10_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f281,f269,f233,f219,f283])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    spl10_27 <=> v1_relat_1(u1_waybel_0(sK4,sK6))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    k4_yellow_2(sK4,u1_waybel_0(sK4,sK6)) = k1_yellow_0(sK4,k2_relat_1(u1_waybel_0(sK4,sK6))) | (~spl10_20 | spl10_22 | ~spl10_27)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f235,f221,f271,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_2)).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    v1_relat_1(u1_waybel_0(sK4,sK6)) | ~spl10_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f269])).
% 0.20/0.49  fof(f280,plain,(
% 0.20/0.49    spl10_28 | ~spl10_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f275,f262,f277])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    spl10_26 <=> m1_subset_1(u1_waybel_0(sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = k2_relat_1(u1_waybel_0(sK4,sK6)) | ~spl10_26),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f264,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    m1_subset_1(u1_waybel_0(sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~spl10_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f262])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    spl10_27 | ~spl10_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f267,f262,f269])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    v1_relat_1(u1_waybel_0(sK4,sK6)) | ~spl10_26),
% 0.20/0.49    inference(resolution,[],[f264,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    spl10_26 | ~spl10_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f259,f241,f262])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    spl10_23 <=> sP3(sK4,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    m1_subset_1(u1_waybel_0(sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~spl10_23),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f243,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP3(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~sP3(X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~sP3(X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    sP3(sK4,sK6) | ~spl10_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f241])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    spl10_23 | ~spl10_4 | ~spl10_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f239,f226,f135,f241])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    spl10_21 <=> l1_struct_0(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    sP3(sK4,sK6) | (~spl10_4 | ~spl10_21)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f228,f137,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP3(X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0,X1] : (sP3(X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(definition_folding,[],[f34,f43])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    l1_struct_0(sK4) | ~spl10_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f226])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    ~spl10_22 | ~spl10_12 | ~spl10_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f237,f219,f175,f233])).
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    ~v2_struct_0(sK4) | (~spl10_12 | ~spl10_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f231,f221])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    ~v2_struct_0(sK4) | ~l1_orders_2(sK4) | ~spl10_12),
% 0.20/0.49    inference(resolution,[],[f85,f177])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    spl10_21 | ~spl10_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f219,f226])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    l1_struct_0(sK4) | ~spl10_20),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f221,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    spl10_20 | ~spl10_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f217,f160,f219])).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    l1_orders_2(sK4) | ~spl10_9),
% 0.20/0.49    inference(resolution,[],[f83,f162])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    spl10_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f200])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    v2_pre_topc(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    spl10_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f195])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    v8_pre_topc(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl10_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f190])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    v3_orders_2(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    spl10_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f67,f185])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    v4_orders_2(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl10_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f180])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v5_orders_2(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl10_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f69,f175])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    v1_lattice3(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    spl10_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f70,f170])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    v2_lattice3(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    spl10_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f71,f165])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    v1_compts_1(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl10_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f160])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    l1_waybel_9(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    spl10_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f73,f155])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ~spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f74,f150])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~v2_struct_0(sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl10_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f75,f145])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    v4_orders_2(sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl10_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f76,f140])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    v7_waybel_0(sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl10_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f77,f135])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    l1_waybel_0(sK6,sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    spl10_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f79,f130])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    v10_waybel_0(sK6,sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl10_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f80,f125])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    r3_waybel_9(sK4,sK6,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ~spl10_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f81,f120])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    sK5 != k1_waybel_2(sK4,sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (28104)------------------------------
% 0.20/0.49  % (28104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28104)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (28104)Memory used [KB]: 11257
% 0.20/0.49  % (28104)Time elapsed: 0.076 s
% 0.20/0.49  % (28104)------------------------------
% 0.20/0.49  % (28104)------------------------------
% 0.20/0.49  % (28091)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (28085)Success in time 0.135 s
%------------------------------------------------------------------------------
