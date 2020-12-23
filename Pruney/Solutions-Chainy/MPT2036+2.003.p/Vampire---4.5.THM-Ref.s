%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  308 ( 714 expanded)
%              Number of leaves         :   51 ( 306 expanded)
%              Depth                    :   27
%              Number of atoms          : 2469 (4754 expanded)
%              Number of equality atoms :   73 ( 192 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f147,f151,f155,f159,f163,f175,f179,f218,f222,f231,f240,f244,f252,f257,f273,f277,f305,f307,f371,f381,f406,f416,f446,f452,f477,f478])).

fof(f478,plain,
    ( sK1 != k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | k1_waybel_2(sK0,sK2) != k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | sK1 = k1_waybel_2(sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f477,plain,
    ( spl6_42
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f476,f450,f363,f352,f275,f177,f173,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f404])).

fof(f404,plain,
    ( spl6_42
  <=> r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f93,plain,
    ( spl6_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f97,plain,
    ( spl6_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f101,plain,
    ( spl6_3
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f105,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f109,plain,
    ( spl6_5
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f113,plain,
    ( spl6_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f117,plain,
    ( spl6_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f121,plain,
    ( spl6_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f125,plain,
    ( spl6_9
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f129,plain,
    ( spl6_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f133,plain,
    ( spl6_11
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f137,plain,
    ( spl6_12
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f149,plain,
    ( spl6_14
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f173,plain,
    ( spl6_18
  <=> r3_waybel_9(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f177,plain,
    ( spl6_19
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f275,plain,
    ( spl6_32
  <=> k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f352,plain,
    ( spl6_38
  <=> m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f363,plain,
    ( spl6_40
  <=> r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f450,plain,
    ( spl6_48
  <=> v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f476,plain,
    ( r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f475,f353])).

fof(f353,plain,
    ( m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f352])).

fof(f475,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_32
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(resolution,[],[f473,f364])).

fof(f364,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f363])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_32
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f472,f276])).

fof(f276,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f275])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f471,f94])).

fof(f94,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f471,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f470,f178])).

fof(f178,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f469,f150])).

fof(f150,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f468,f102])).

fof(f102,plain,
    ( v7_waybel_0(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f467,f98])).

fof(f98,plain,
    ( v4_orders_2(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f467,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_48 ),
    inference(resolution,[],[f462,f174])).

fof(f174,plain,
    ( r3_waybel_9(sK0,sK2,sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f462,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f461,f106])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f461,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f460,f138])).

fof(f138,plain,
    ( l1_waybel_9(sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f460,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f459,f134])).

fof(f134,plain,
    ( v1_compts_1(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f459,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f458,f130])).

fof(f130,plain,
    ( v2_lattice3(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f458,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f457,f126])).

fof(f126,plain,
    ( v1_lattice3(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f457,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f456,f122])).

fof(f122,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f456,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f455,f118])).

fof(f118,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f455,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f454,f114])).

fof(f114,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f454,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_5
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f453,f110])).

fof(f110,plain,
    ( v8_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f453,plain,
    ( ! [X2,X0,X1] :
        ( ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r3_orders_2(sK0,X1,X2) )
    | ~ spl6_48 ),
    inference(resolution,[],[f451,f89])).

fof(f89,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r3_orders_2(X0,X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r3_orders_2(X0,X3,X5) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r3_orders_2(X0,X3,X5) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).

fof(f451,plain,
    ( v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f450])).

fof(f452,plain,
    ( spl6_48
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f448,f250,f450])).

fof(f250,plain,
    ( spl6_29
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f448,plain,
    ( v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ spl6_29 ),
    inference(resolution,[],[f251,f41])).

fof(f41,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).

fof(f251,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f250])).

fof(f446,plain,
    ( spl6_47
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f427,f414,f303,f177,f153,f121,f444])).

fof(f444,plain,
    ( spl6_47
  <=> sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f153,plain,
    ( spl6_15
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f303,plain,
    ( spl6_36
  <=> r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f414,plain,
    ( spl6_43
  <=> r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f427,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f426,f122])).

fof(f426,plain,
    ( ~ v5_orders_2(sK0)
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f425,f304])).

fof(f304,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f425,plain,
    ( ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f424,f178])).

fof(f424,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f418,f154])).

fof(f154,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f418,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_43 ),
    inference(resolution,[],[f415,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f415,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f414])).

fof(f416,plain,
    ( spl6_43
    | ~ spl6_6
    | ~ spl6_15
    | spl6_17
    | ~ spl6_19
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f412,f404,f352,f177,f161,f153,f113,f414])).

fof(f161,plain,
    ( spl6_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f412,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_6
    | ~ spl6_15
    | spl6_17
    | ~ spl6_19
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f411,f162])).

fof(f162,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f411,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f410,f353])).

fof(f410,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f409,f178])).

fof(f409,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f408,f154])).

fof(f408,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f407,f114])).

fof(f407,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | v2_struct_0(sK0)
    | ~ spl6_42 ),
    inference(resolution,[],[f405,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f405,plain,
    ( r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f404])).

fof(f406,plain,
    ( spl6_42
    | ~ spl6_24
    | ~ spl6_28
    | ~ spl6_38
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f388,f363,f352,f247,f229,f404])).

fof(f229,plain,
    ( spl6_24
  <=> m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f247,plain,
    ( spl6_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK1,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f388,plain,
    ( r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_24
    | ~ spl6_28
    | ~ spl6_38
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f383,f353])).

fof(f383,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_24
    | ~ spl6_28
    | ~ spl6_40 ),
    inference(resolution,[],[f364,f253])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f248,f233])).

fof(f233,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2))
    | ~ spl6_24 ),
    inference(resolution,[],[f230,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f230,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK1,X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f381,plain,
    ( spl6_38
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | spl6_21
    | ~ spl6_31
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f380,f303,f271,f216,f177,f153,f121,f352])).

fof(f216,plain,
    ( spl6_21
  <=> sK1 = k1_waybel_2(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f271,plain,
    ( spl6_31
  <=> k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f380,plain,
    ( m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | spl6_21
    | ~ spl6_31
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f379,f217])).

fof(f217,plain,
    ( sK1 != k1_waybel_2(sK0,sK2)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f379,plain,
    ( sK1 = k1_waybel_2(sK0,sK2)
    | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_31
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f378,f272])).

fof(f272,plain,
    ( k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f378,plain,
    ( m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f377,f122])).

fof(f377,plain,
    ( ~ v5_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f376,f178])).

fof(f376,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f330,f154])).

fof(f330,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_36 ),
    inference(resolution,[],[f304,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f371,plain,
    ( spl6_40
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | spl6_21
    | ~ spl6_31
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f370,f303,f271,f216,f177,f153,f121,f363])).

fof(f370,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | spl6_21
    | ~ spl6_31
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f369,f217])).

fof(f369,plain,
    ( sK1 = k1_waybel_2(sK0,sK2)
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_31
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f368,f272])).

fof(f368,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f367,f122])).

fof(f367,plain,
    ( ~ v5_orders_2(sK0)
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f366,f178])).

fof(f366,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f331,f154])).

fof(f331,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_36 ),
    inference(resolution,[],[f304,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f307,plain,
    ( spl6_36
    | ~ spl6_25
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f306,f275,f235,f303])).

fof(f235,plain,
    ( spl6_25
  <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f306,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_25
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f236,f276])).

fof(f236,plain,
    ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f235])).

fof(f305,plain,
    ( spl6_36
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f301,f275,f255,f177,f173,f157,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f303])).

fof(f157,plain,
    ( spl6_16
  <=> v10_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f255,plain,
    ( spl6_30
  <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f301,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f300,f276])).

fof(f300,plain,
    ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f299,f94])).

fof(f299,plain,
    ( v2_struct_0(sK2)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f298,f158])).

fof(f158,plain,
    ( v10_waybel_0(sK2,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f298,plain,
    ( ~ v10_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f297,f178])).

fof(f297,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f296,f150])).

fof(f296,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f295,f102])).

fof(f295,plain,
    ( ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f294,f98])).

fof(f294,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(resolution,[],[f267,f174])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v10_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f266,f106])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f265,f138])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f264,f134])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f263,f130])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f262,f126])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f261,f122])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f260,f118])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f259,f114])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f258,f110])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v10_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_30 ),
    inference(resolution,[],[f256,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v10_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ v10_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ v10_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).

fof(f256,plain,
    ( v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f255])).

fof(f277,plain,
    ( spl6_32
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f233,f229,f275])).

fof(f273,plain,
    ( spl6_31
    | ~ spl6_15
    | spl6_17
    | ~ spl6_22
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f269,f242,f220,f161,f153,f271])).

fof(f220,plain,
    ( spl6_22
  <=> k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f242,plain,
    ( spl6_27
  <=> v1_relat_1(u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f269,plain,
    ( k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | spl6_17
    | ~ spl6_22
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f268,f221])).

fof(f221,plain,
    ( k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f268,plain,
    ( k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_15
    | spl6_17
    | ~ spl6_27 ),
    inference(resolution,[],[f171,f243])).

fof(f243,plain,
    ( v1_relat_1(u1_waybel_0(sK0,sK2))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f242])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_yellow_2(sK0,X0) = k1_yellow_0(sK0,k2_relat_1(X0)) )
    | ~ spl6_15
    | spl6_17 ),
    inference(subsumption_resolution,[],[f170,f162])).

fof(f170,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v1_relat_1(X0)
        | k4_yellow_2(sK0,X0) = k1_yellow_0(sK0,k2_relat_1(X0)) )
    | ~ spl6_15 ),
    inference(resolution,[],[f154,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_relat_1(X1)
      | k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_2)).

fof(f257,plain,
    ( spl6_30
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f245,f238,f255])).

fof(f238,plain,
    ( spl6_26
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f245,plain,
    ( v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
    | ~ spl6_26 ),
    inference(resolution,[],[f239,f41])).

fof(f239,plain,
    ( m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f252,plain,
    ( spl6_28
    | spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f214,f177,f173,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f250,f247])).

fof(f214,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f213,f106])).

fof(f213,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f212,f178])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f211,f150])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f210,f102])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f209,f98])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f208,f94])).

fof(f208,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f207,f138])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f206,f134])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f205,f130])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f204,f126])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f203,f122])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f202,f118])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f201,f114])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f185,f110])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r3_orders_2(sK0,sK1,X0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f174,f88])).

fof(f88,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ r3_waybel_9(X0,X1,X3)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r3_orders_2(X0,X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r3_orders_2(X0,X3,X5) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r3_orders_2(X0,X3,X5) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f244,plain,
    ( spl6_27
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f232,f229,f242])).

fof(f232,plain,
    ( v1_relat_1(u1_waybel_0(sK0,sK2))
    | ~ spl6_24 ),
    inference(resolution,[],[f230,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f240,plain,
    ( spl6_25
    | spl6_26
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f200,f177,f173,f157,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f238,f235])).

fof(f200,plain,
    ( m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f199,f106])).

fof(f199,plain,
    ( m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f198,f158])).

fof(f198,plain,
    ( m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f197,f178])).

fof(f197,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f196,f150])).

fof(f196,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f195,f102])).

fof(f195,plain,
    ( ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f194,f98])).

fof(f194,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f193,f94])).

fof(f193,plain,
    ( v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f192,f138])).

fof(f192,plain,
    ( ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f191,f134])).

fof(f191,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f190,f130])).

fof(f190,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f189,f126])).

fof(f189,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f188,f122])).

fof(f188,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f187,f118])).

fof(f187,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f186,f114])).

fof(f186,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f184,f110])).

fof(f184,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ v10_waybel_0(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f174,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ r3_waybel_9(X0,X1,X3)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v10_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v10_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v10_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f231,plain,
    ( spl6_24
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f169,f149,f145,f229])).

fof(f145,plain,
    ( spl6_13
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f169,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f164,f168])).

fof(f168,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_13 ),
    inference(resolution,[],[f146,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f146,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f164,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_14 ),
    inference(resolution,[],[f150,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f222,plain,
    ( spl6_22
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17 ),
    inference(avatar_split_clause,[],[f167,f161,f153,f149,f220])).

fof(f167,plain,
    ( k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17 ),
    inference(subsumption_resolution,[],[f166,f162])).

fof(f166,plain,
    ( v2_struct_0(sK0)
    | k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f165,f154])).

fof(f165,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl6_14 ),
    inference(resolution,[],[f150,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_2)).

fof(f218,plain,(
    ~ spl6_21 ),
    inference(avatar_split_clause,[],[f48,f216])).

fof(f48,plain,(
    sK1 != k1_waybel_2(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f179,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f49,f177])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f175,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f47,f173])).

fof(f47,plain,(
    r3_waybel_9(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f163,plain,
    ( ~ spl6_17
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f143,f137,f125,f161])).

fof(f143,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f140,f142])).

fof(f142,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f138,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f140,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f126,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f159,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f46,f157])).

fof(f46,plain,(
    v10_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,
    ( spl6_15
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f142,f137,f153])).

fof(f151,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f45,f149])).

fof(f45,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f147,plain,
    ( spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f141,f137,f145])).

fof(f141,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f138,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f58,f137])).

fof(f58,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f135,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f57,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f131,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f56,f129])).

fof(f56,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f127,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f55,f125])).

fof(f55,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f123,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f119,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f53,f117])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f115,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f111,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f50,f105])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f99,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (22190)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (22187)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (22198)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (22182)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (22195)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (22191)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (22196)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (22188)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (22185)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (22186)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (22189)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (22182)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f479,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f147,f151,f155,f159,f163,f175,f179,f218,f222,f231,f240,f244,f252,f257,f273,f277,f305,f307,f371,f381,f406,f416,f446,f452,f477,f478])).
% 0.21/0.50  fof(f478,plain,(
% 0.21/0.50    sK1 != k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | k1_waybel_2(sK0,sK2) != k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | sK1 = k1_waybel_2(sK0,sK2)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f477,plain,(
% 0.21/0.50    spl6_42 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_32 | ~spl6_38 | ~spl6_40 | ~spl6_48),
% 0.21/0.50    inference(avatar_split_clause,[],[f476,f450,f363,f352,f275,f177,f173,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f404])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    spl6_42 <=> r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl6_1 <=> v2_struct_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl6_2 <=> v4_orders_2(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl6_3 <=> v7_waybel_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl6_4 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl6_5 <=> v8_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl6_6 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl6_7 <=> v4_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl6_8 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl6_9 <=> v1_lattice3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl6_10 <=> v2_lattice3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl6_11 <=> v1_compts_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl6_12 <=> l1_waybel_9(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl6_14 <=> l1_waybel_0(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl6_18 <=> r3_waybel_9(sK0,sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl6_19 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    spl6_32 <=> k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    spl6_38 <=> m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    spl6_40 <=> r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    spl6_48 <=> v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_32 | ~spl6_38 | ~spl6_40 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f475,f353])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~spl6_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f352])).
% 0.21/0.50  fof(f475,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_32 | ~spl6_40 | ~spl6_48)),
% 0.21/0.50    inference(resolution,[],[f473,f364])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~spl6_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f363])).
% 0.21/0.50  fof(f473,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_32 | ~spl6_48)),
% 0.21/0.50    inference(forward_demodulation,[],[f472,f276])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2)) | ~spl6_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f275])).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f471,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~v2_struct_0(sK2) | spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f470,f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f177])).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f469,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    l1_waybel_0(sK2,sK0) | ~spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f468,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    v7_waybel_0(sK2) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    ( ! [X0] : (~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f467,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    v4_orders_2(sK2) | ~spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18 | ~spl6_48)),
% 0.21/0.50    inference(resolution,[],[f462,f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    r3_waybel_9(sK0,sK2,sK1) | ~spl6_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f173])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f461,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f461,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f460,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    l1_waybel_9(sK0) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f459,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v1_compts_1(sK0) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f133])).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f458,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    v2_lattice3(sK0) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f457,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    v1_lattice3(sK0) | ~spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f456,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f456,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f455,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    v4_orders_2(sK0) | ~spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f455,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f454,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    v3_orders_2(sK0) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | (~spl6_5 | ~spl6_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f453,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v8_pre_topc(sK0) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r3_orders_2(sK0,X1,X2)) ) | ~spl6_48),
% 0.21/0.50    inference(resolution,[],[f451,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0,X5,X3,X1] : (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r3_orders_2(X0,X3,X5)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r3_orders_2(X0,X3,X5)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r3_orders_2(X0,X3,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.21/0.50    inference(rectify,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).
% 0.21/0.50  fof(f451,plain,(
% 0.21/0.50    v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~spl6_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f450])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    spl6_48 | ~spl6_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f448,f250,f450])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    spl6_29 <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~spl6_29),
% 0.21/0.50    inference(resolution,[],[f251,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~spl6_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f250])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    spl6_47 | ~spl6_8 | ~spl6_15 | ~spl6_19 | ~spl6_36 | ~spl6_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f427,f414,f303,f177,f153,f121,f444])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    spl6_47 <=> sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl6_15 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    spl6_36 <=> r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    spl6_43 <=> r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_15 | ~spl6_19 | ~spl6_36 | ~spl6_43)),
% 0.21/0.50    inference(subsumption_resolution,[],[f426,f122])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_19 | ~spl6_36 | ~spl6_43)),
% 0.21/0.50    inference(subsumption_resolution,[],[f425,f304])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~spl6_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f303])).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~v5_orders_2(sK0) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_19 | ~spl6_43)),
% 0.21/0.50    inference(subsumption_resolution,[],[f424,f178])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~v5_orders_2(sK0) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_43)),
% 0.21/0.50    inference(subsumption_resolution,[],[f418,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl6_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f153])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~v5_orders_2(sK0) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~spl6_43),
% 0.21/0.50    inference(resolution,[],[f415,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~v5_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.50    inference(rectify,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~spl6_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f414])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    spl6_43 | ~spl6_6 | ~spl6_15 | spl6_17 | ~spl6_19 | ~spl6_38 | ~spl6_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f412,f404,f352,f177,f161,f153,f113,f414])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl6_17 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (~spl6_6 | ~spl6_15 | spl6_17 | ~spl6_19 | ~spl6_38 | ~spl6_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f411,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl6_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f161])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_15 | ~spl6_19 | ~spl6_38 | ~spl6_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f410,f353])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_15 | ~spl6_19 | ~spl6_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f409,f178])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_15 | ~spl6_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f408,f154])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f407,f114])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | v2_struct_0(sK0) | ~spl6_42),
% 0.21/0.50    inference(resolution,[],[f405,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~spl6_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f404])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    spl6_42 | ~spl6_24 | ~spl6_28 | ~spl6_38 | ~spl6_40),
% 0.21/0.50    inference(avatar_split_clause,[],[f388,f363,f352,f247,f229,f404])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl6_24 <=> m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    spl6_28 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (~spl6_24 | ~spl6_28 | ~spl6_38 | ~spl6_40)),
% 0.21/0.50    inference(subsumption_resolution,[],[f383,f353])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (~spl6_24 | ~spl6_28 | ~spl6_40)),
% 0.21/0.50    inference(resolution,[],[f364,f253])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_24 | ~spl6_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f248,f233])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2)) | ~spl6_24),
% 0.21/0.50    inference(resolution,[],[f230,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl6_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f229])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | ~spl6_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f247])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    spl6_38 | ~spl6_8 | ~spl6_15 | ~spl6_19 | spl6_21 | ~spl6_31 | ~spl6_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f380,f303,f271,f216,f177,f153,f121,f352])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    spl6_21 <=> sK1 = k1_waybel_2(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl6_31 <=> k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | (~spl6_8 | ~spl6_15 | ~spl6_19 | spl6_21 | ~spl6_31 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f379,f217])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    sK1 != k1_waybel_2(sK0,sK2) | spl6_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f216])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    sK1 = k1_waybel_2(sK0,sK2) | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | (~spl6_8 | ~spl6_15 | ~spl6_19 | ~spl6_31 | ~spl6_36)),
% 0.21/0.50    inference(forward_demodulation,[],[f378,f272])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~spl6_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f271])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_15 | ~spl6_19 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f377,f122])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_19 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f376,f178])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f154])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~spl6_36),
% 0.21/0.50    inference(resolution,[],[f304,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_lattice3(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    spl6_40 | ~spl6_8 | ~spl6_15 | ~spl6_19 | spl6_21 | ~spl6_31 | ~spl6_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f370,f303,f271,f216,f177,f153,f121,f363])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (~spl6_8 | ~spl6_15 | ~spl6_19 | spl6_21 | ~spl6_31 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f369,f217])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    sK1 = k1_waybel_2(sK0,sK2) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | (~spl6_8 | ~spl6_15 | ~spl6_19 | ~spl6_31 | ~spl6_36)),
% 0.21/0.50    inference(forward_demodulation,[],[f368,f272])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_15 | ~spl6_19 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f367,f122])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_19 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f366,f178])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f154])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~spl6_36),
% 0.21/0.50    inference(resolution,[],[f304,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_lattice3(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | r2_lattice3(X0,X2,sK5(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    spl6_36 | ~spl6_25 | ~spl6_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f306,f275,f235,f303])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl6_25 <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | (~spl6_25 | ~spl6_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f236,f276])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~spl6_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f235])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    spl6_36 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_30 | ~spl6_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f301,f275,f255,f177,f173,f157,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f303])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl6_16 <=> v10_waybel_0(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    spl6_30 <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_30 | ~spl6_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f300,f276])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f299,f94])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    v2_struct_0(sK2) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f298,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    v10_waybel_0(sK2,sK0) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f157])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    ~v10_waybel_0(sK2,sK0) | v2_struct_0(sK2) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f297,f178])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | v2_struct_0(sK2) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f296,f150])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | v2_struct_0(sK2) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f295,f102])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | v2_struct_0(sK2) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f294,f98])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | v2_struct_0(sK2) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18 | ~spl6_30)),
% 0.21/0.50    inference(resolution,[],[f267,f174])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f266,f106])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f265,f138])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f264,f134])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f263,f130])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f262,f126])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f261,f122])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f260,f118])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f114])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f258,f110])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v10_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | ~spl6_30),
% 0.21/0.50    inference(resolution,[],[f256,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v10_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~v10_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.50    inference(equality_resolution,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~v10_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X2) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~spl6_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f255])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    spl6_32 | ~spl6_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f233,f229,f275])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    spl6_31 | ~spl6_15 | spl6_17 | ~spl6_22 | ~spl6_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f269,f242,f220,f161,f153,f271])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl6_22 <=> k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    spl6_27 <=> v1_relat_1(u1_waybel_0(sK0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | spl6_17 | ~spl6_22 | ~spl6_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f268,f221])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~spl6_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f220])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_15 | spl6_17 | ~spl6_27)),
% 0.21/0.50    inference(resolution,[],[f171,f243])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    v1_relat_1(u1_waybel_0(sK0,sK2)) | ~spl6_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f242])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k4_yellow_2(sK0,X0) = k1_yellow_0(sK0,k2_relat_1(X0))) ) | (~spl6_15 | spl6_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f162])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~v1_relat_1(X0) | k4_yellow_2(sK0,X0) = k1_yellow_0(sK0,k2_relat_1(X0))) ) | ~spl6_15),
% 0.21/0.50    inference(resolution,[],[f154,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~v1_relat_1(X1) | k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_2)).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    spl6_30 | ~spl6_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f245,f238,f255])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    spl6_26 <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~spl6_26),
% 0.21/0.50    inference(resolution,[],[f239,f41])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~spl6_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f238])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    spl6_28 | spl6_29 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f177,f173,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f250,f247])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f213,f106])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f212,f178])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f211,f150])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f102])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ( ! [X0] : (~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f209,f98])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (spl6_1 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f208,f94])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f207,f138])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f206,f134])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f130])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f204,f126])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f203,f122])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X0] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f202,f118])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f201,f114])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | (~spl6_5 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f110])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0] : (~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,sK1,X0)) ) | ~spl6_18),
% 0.21/0.50    inference(resolution,[],[f174,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0,X5,X3,X1] : (~r3_waybel_9(X0,X1,X3) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r3_orders_2(X0,X3,X5)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r3_orders_2(X0,X3,X5)) )),
% 0.21/0.50    inference(equality_resolution,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r3_orders_2(X0,X3,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    spl6_27 | ~spl6_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f232,f229,f242])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    v1_relat_1(u1_waybel_0(sK0,sK2)) | ~spl6_24),
% 0.21/0.50    inference(resolution,[],[f230,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    spl6_25 | spl6_26 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f177,f173,f157,f149,f137,f133,f129,f125,f121,f117,f113,f109,f105,f101,f97,f93,f238,f235])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f106])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_16 | ~spl6_18 | ~spl6_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f198,f158])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18 | ~spl6_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f178])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f196,f150])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f195,f102])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f194,f98])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f193,f94])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f192,f138])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f134])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f130])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f126])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f122])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f118])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_6 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f114])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_5 | ~spl6_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f110])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v10_waybel_0(sK2,sK0) | ~v2_pre_topc(sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~spl6_18),
% 0.21/0.50    inference(resolution,[],[f174,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r3_waybel_9(X0,X1,X3) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v10_waybel_0(X1,X0) | ~v2_pre_topc(X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v10_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v10_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X2) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    spl6_24 | ~spl6_13 | ~spl6_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f169,f149,f145,f229])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl6_13 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (~spl6_13 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl6_13),
% 0.21/0.50    inference(resolution,[],[f146,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl6_14),
% 0.21/0.50    inference(resolution,[],[f150,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl6_22 | ~spl6_14 | ~spl6_15 | spl6_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f167,f161,f153,f149,f220])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | (~spl6_14 | ~spl6_15 | spl6_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f166,f162])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    v2_struct_0(sK0) | k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | (~spl6_14 | ~spl6_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f165,f154])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~spl6_14),
% 0.21/0.50    inference(resolution,[],[f150,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_2)).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~spl6_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f216])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    sK1 != k1_waybel_2(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    spl6_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f177])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl6_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f173])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    r3_waybel_9(sK0,sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~spl6_17 | ~spl6_9 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f143,f137,f125,f161])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | (~spl6_9 | ~spl6_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f140,f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl6_12),
% 0.21/0.50    inference(resolution,[],[f138,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~v2_struct_0(sK0) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f126,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl6_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f157])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v10_waybel_0(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl6_15 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f142,f137,f153])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl6_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f149])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    l1_waybel_0(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl6_13 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f141,f137,f145])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl6_12),
% 0.21/0.50    inference(resolution,[],[f138,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f137])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    l1_waybel_9(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl6_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f133])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v1_compts_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f129])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v2_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f125])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f121])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f117])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f113])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f109])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v8_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f105])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f101])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v7_waybel_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f97])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v4_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f93])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (22182)------------------------------
% 0.21/0.50  % (22182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22182)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (22182)Memory used [KB]: 6524
% 0.21/0.50  % (22182)Time elapsed: 0.075 s
% 0.21/0.50  % (22182)------------------------------
% 0.21/0.50  % (22182)------------------------------
% 0.21/0.50  % (22181)Success in time 0.141 s
%------------------------------------------------------------------------------
