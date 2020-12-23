%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 496 expanded)
%              Number of leaves         :   50 ( 254 expanded)
%              Depth                    :    7
%              Number of atoms          :  899 (1904 expanded)
%              Number of equality atoms :   66 ( 115 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f95,f99,f103,f107,f111,f121,f126,f130,f135,f147,f158,f162,f181,f185,f197,f233,f544,f867,f878,f884,f1012,f1018,f1060,f1066,f1089,f1110,f1132,f2356,f2376,f2624,f2627])).

fof(f2627,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_57
    | ~ spl3_66
    | spl3_68
    | ~ spl3_101 ),
    inference(avatar_contradiction_clause,[],[f2626])).

fof(f2626,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_57
    | ~ spl3_66
    | spl3_68
    | ~ spl3_101 ),
    inference(subsumption_resolution,[],[f2382,f2625])).

fof(f2625,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_57
    | ~ spl3_66
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f2623,f2358])).

fof(f2358,plain,
    ( sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_57
    | ~ spl3_66 ),
    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f81,f81,f2355,f1131])).

fof(f1131,plain,
    ( ! [X4,X5,X3] :
        ( k11_lattice3(X3,X4,X5) = X4
        | ~ r3_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v3_orders_2(X3) )
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1130,plain,
    ( spl3_57
  <=> ! [X3,X5,X4] :
        ( k11_lattice3(X3,X4,X5) = X4
        | ~ r3_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v3_orders_2(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f2355,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2353,plain,
    ( spl3_66
  <=> r3_orders_2(k2_yellow_1(sK0),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f81,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( ! [X0] : l1_orders_2(k2_yellow_1(X0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_10
  <=> ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f71,plain,
    ( v2_lattice3(k2_yellow_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_2
  <=> v2_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( ! [X0] : v5_orders_2(k2_yellow_1(X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_9
  <=> ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f94,plain,
    ( ! [X0] : v3_orders_2(k2_yellow_1(X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_7
  <=> ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f2623,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_101 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f2621,plain,
    ( spl3_101
  <=> k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f2382,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_21
    | ~ spl3_28
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f81,f543,f2375,f180])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( k12_lattice3(X0,X1,X2) != X1
        | r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( r3_orders_2(X0,X1,X2)
        | k12_lattice3(X0,X1,X2) != X1
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f2375,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_68 ),
    inference(avatar_component_clause,[],[f2373])).

fof(f2373,plain,
    ( spl3_68
  <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f543,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl3_28
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f2624,plain,
    ( spl3_101
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f842,f541,f195,f160,f105,f101,f97,f79,f74,f69,f2621])).

fof(f74,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f97,plain,
    ( spl3_8
  <=> ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f160,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f195,plain,
    ( spl3_23
  <=> ! [X1,X3,X0,X2] :
        ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f842,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f572,f204])).

fof(f204,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f102,f71,f106,f98,f76,f81,f81,f196])).

fof(f196,plain,
    ( ! [X2,X0,X3,X1] :
        ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f76,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f98,plain,
    ( ! [X0] : v4_orders_2(k2_yellow_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f572,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f102,f71,f106,f81,f543,f161])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f2376,plain,
    ( ~ spl3_68
    | spl3_1
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_28
    | spl3_30 ),
    inference(avatar_split_clause,[],[f873,f864,f541,f145,f79,f64,f2373])).

fof(f64,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f145,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f864,plain,
    ( spl3_30
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f873,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_1
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_28
    | spl3_30 ),
    inference(unit_resulting_resolution,[],[f66,f81,f543,f866,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | v1_xboole_0(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f866,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f864])).

fof(f66,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f2356,plain,
    ( spl3_66
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15
    | spl3_16 ),
    inference(avatar_split_clause,[],[f164,f132,f128,f105,f93,f79,f74,f2353])).

fof(f128,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r3_orders_2(X0,X1,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f132,plain,
    ( spl3_16
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f106,f94,f76,f81,f134,f129])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(X0))
        | r3_orders_2(X0,X1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f134,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1132,plain,
    ( spl3_57
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f193,f183,f160,f1130])).

fof(f183,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( k12_lattice3(X0,X1,X2) = X1
        | ~ r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f193,plain,
    ( ! [X4,X5,X3] :
        ( k11_lattice3(X3,X4,X5) = X4
        | ~ r3_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v3_orders_2(X3) )
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X4,X5,X3] :
        ( k11_lattice3(X3,X4,X5) = X4
        | ~ r3_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v3_orders_2(X3)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3) )
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(superposition,[],[f184,f161])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( k12_lattice3(X0,X1,X2) = X1
        | ~ r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f1110,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_28
    | spl3_29
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(avatar_contradiction_clause,[],[f1109])).

fof(f1109,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_28
    | spl3_29
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f872,f1091])).

fof(f1091,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f76,f543,f1065,f1088])).

fof(f1088,plain,
    ( ! [X2,X0,X1] :
        ( k11_lattice3(X0,X1,X2) != X1
        | r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1087,plain,
    ( spl3_54
  <=> ! [X1,X0,X2] :
        ( k11_lattice3(X0,X1,X2) != X1
        | r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f1065,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1063,plain,
    ( spl3_52
  <=> k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f872,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_28
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f66,f76,f543,f862,f146])).

fof(f862,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f860])).

fof(f860,plain,
    ( spl3_29
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f1089,plain,
    ( spl3_54
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f187,f179,f160,f1087])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( k11_lattice3(X0,X1,X2) != X1
        | r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( k11_lattice3(X0,X1,X2) != X1
        | r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(superposition,[],[f180,f161])).

fof(f1066,plain,
    ( spl3_52
    | ~ spl3_47
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f1061,f1057,f1015,f1063])).

fof(f1015,plain,
    ( spl3_47
  <=> k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1057,plain,
    ( spl3_51
  <=> k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f1061,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_47
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f1059,f1017])).

fof(f1017,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1059,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f1057])).

fof(f1060,plain,
    ( spl3_51
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f226,f195,f156,f105,f101,f97,f79,f74,f69,f1057])).

fof(f156,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f226,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f200,f167])).

fof(f167,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f102,f71,f106,f76,f81,f157])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f200,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f102,f71,f106,f98,f76,f81,f76,f196])).

fof(f1018,plain,
    ( spl3_47
    | ~ spl3_32
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f1013,f1009,f881,f1015])).

fof(f881,plain,
    ( spl3_32
  <=> sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1009,plain,
    ( spl3_46
  <=> k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1013,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_32
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f1011,f883])).

fof(f883,plain,
    ( sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1011,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1012,plain,
    ( spl3_46
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f202,f195,f105,f101,f97,f79,f74,f69,f1009])).

fof(f202,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f102,f71,f106,f98,f76,f76,f81,f196])).

fof(f884,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_24
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f879,f875,f230,f183,f105,f101,f93,f74,f69,f881])).

fof(f230,plain,
    ( spl3_24
  <=> r3_orders_2(k2_yellow_1(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f875,plain,
    ( spl3_31
  <=> k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f879,plain,
    ( sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_24
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f877,f869])).

fof(f869,plain,
    ( sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f76,f76,f232,f184])).

fof(f232,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f230])).

fof(f877,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f875])).

fof(f878,plain,
    ( spl3_31
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f173,f160,f105,f101,f74,f69,f875])).

fof(f173,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f102,f71,f106,f76,f76,f161])).

fof(f867,plain,
    ( ~ spl3_29
    | ~ spl3_30
    | spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f122,f119,f84,f864,f860])).

fof(f84,plain,
    ( spl3_5
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f122,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_5
    | ~ spl3_13 ),
    inference(resolution,[],[f120,f86])).

fof(f86,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f544,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f138,f124,f105,f79,f74,f541])).

fof(f124,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f138,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f106,f76,f81,f125])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f124])).

% (16963)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f233,plain,
    ( spl3_24
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15
    | spl3_16 ),
    inference(avatar_split_clause,[],[f163,f132,f128,f105,f93,f74,f230])).

fof(f163,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f106,f94,f76,f76,f134,f129])).

fof(f197,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f58,f195])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
      | ~ v4_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( v4_orders_2(X0)
                   => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).

fof(f185,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f56,f183])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = X1
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f181,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f55,f179])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f162,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f60,f160])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f158,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f57,f156])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f147,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f52,f145])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f135,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f116,f109,f105,f69,f132])).

fof(f109,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ v2_lattice3(X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f106,f71,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v2_lattice3(X0)
        | ~ v2_struct_0(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f130,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f59,f128])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f126,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f61,f124])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f121,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f62,f119])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f111,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f107,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f51,f105])).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f103,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f99,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f48,f97])).

fof(f48,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f42,f74])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f69])).

fof(f41,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f64])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 11:38:56 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.44  % (16956)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (16955)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (16953)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (16965)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (16958)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (16954)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (16962)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (16966)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (16951)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (16964)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (16957)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (16959)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (16967)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (16960)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (16952)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.53  % (16961)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (16949)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.53  % (16955)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f2628,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f95,f99,f103,f107,f111,f121,f126,f130,f135,f147,f158,f162,f181,f185,f197,f233,f544,f867,f878,f884,f1012,f1018,f1060,f1066,f1089,f1110,f1132,f2356,f2376,f2624,f2627])).
% 0.21/0.53  fof(f2627,plain,(
% 0.21/0.53    ~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_21 | ~spl3_28 | ~spl3_57 | ~spl3_66 | spl3_68 | ~spl3_101),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f2626])).
% 0.21/0.53  fof(f2626,plain,(
% 0.21/0.53    $false | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_21 | ~spl3_28 | ~spl3_57 | ~spl3_66 | spl3_68 | ~spl3_101)),
% 0.21/0.53    inference(subsumption_resolution,[],[f2382,f2625])).
% 0.21/0.53  fof(f2625,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_57 | ~spl3_66 | ~spl3_101)),
% 0.21/0.53    inference(forward_demodulation,[],[f2623,f2358])).
% 0.21/0.53  fof(f2358,plain,(
% 0.21/0.53    sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_57 | ~spl3_66)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f81,f81,f2355,f1131])).
% 0.21/0.53  fof(f1131,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k11_lattice3(X3,X4,X5) = X4 | ~r3_orders_2(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3)) ) | ~spl3_57),
% 0.21/0.53    inference(avatar_component_clause,[],[f1130])).
% 0.21/0.53  fof(f1130,plain,(
% 0.21/0.53    spl3_57 <=> ! [X3,X5,X4] : (k11_lattice3(X3,X4,X5) = X4 | ~r3_orders_2(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.53  fof(f2355,plain,(
% 0.21/0.53    r3_orders_2(k2_yellow_1(sK0),sK2,sK2) | ~spl3_66),
% 0.21/0.53    inference(avatar_component_clause,[],[f2353])).
% 0.21/0.53  fof(f2353,plain,(
% 0.21/0.53    spl3_66 <=> r3_orders_2(k2_yellow_1(sK0),sK2,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl3_4 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) ) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl3_10 <=> ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    v2_lattice3(k2_yellow_1(sK0)) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl3_2 <=> v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) ) | ~spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl3_9 <=> ! [X0] : v5_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) ) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl3_7 <=> ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f2623,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~spl3_101),
% 0.21/0.53    inference(avatar_component_clause,[],[f2621])).
% 0.21/0.53  fof(f2621,plain,(
% 0.21/0.53    spl3_101 <=> k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 0.21/0.53  fof(f2382,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_21 | ~spl3_28 | spl3_68)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f81,f543,f2375,f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) ) | ~spl3_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    spl3_21 <=> ! [X1,X0,X2] : (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.53  fof(f2375,plain,(
% 0.21/0.53    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl3_68),
% 0.21/0.53    inference(avatar_component_clause,[],[f2373])).
% 0.21/0.53  fof(f2373,plain,(
% 0.21/0.53    spl3_68 <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.21/0.53  fof(f543,plain,(
% 0.21/0.53    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~spl3_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f541])).
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    spl3_28 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.53  fof(f2624,plain,(
% 0.21/0.53    spl3_101 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_20 | ~spl3_23 | ~spl3_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f842,f541,f195,f160,f105,f101,f97,f79,f74,f69,f2621])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl3_8 <=> ! [X0] : v4_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl3_20 <=> ! [X1,X0,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl3_23 <=> ! [X1,X3,X0,X2] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.53  fof(f842,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_20 | ~spl3_23 | ~spl3_28)),
% 0.21/0.53    inference(forward_demodulation,[],[f572,f204])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_23)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f102,f71,f106,f98,f76,f81,f81,f196])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) ) | ~spl3_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f195])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) ) | ~spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f572,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_20 | ~spl3_28)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f102,f71,f106,f81,f543,f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) ) | ~spl3_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f160])).
% 0.21/0.53  fof(f2376,plain,(
% 0.21/0.53    ~spl3_68 | spl3_1 | ~spl3_4 | ~spl3_17 | ~spl3_28 | spl3_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f873,f864,f541,f145,f79,f64,f2373])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl3_1 <=> v1_xboole_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    spl3_17 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.53  fof(f864,plain,(
% 0.21/0.53    spl3_30 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.53  fof(f873,plain,(
% 0.21/0.53    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (spl3_1 | ~spl3_4 | ~spl3_17 | ~spl3_28 | spl3_30)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f66,f81,f543,f866,f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) ) | ~spl3_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f145])).
% 0.21/0.53  fof(f866,plain,(
% 0.21/0.53    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl3_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f864])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f64])).
% 0.21/0.53  fof(f2356,plain,(
% 0.21/0.53    spl3_66 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_15 | spl3_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f164,f132,f128,f105,f93,f79,f74,f2353])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl3_15 <=> ! [X1,X0,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl3_16 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    r3_orders_2(k2_yellow_1(sK0),sK2,sK2) | (~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_15 | spl3_16)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f106,f94,f76,f81,f134,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~v2_struct_0(k2_yellow_1(sK0)) | spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f1132,plain,(
% 0.21/0.53    spl3_57 | ~spl3_20 | ~spl3_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f183,f160,f1130])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl3_22 <=> ! [X1,X0,X2] : (k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k11_lattice3(X3,X4,X5) = X4 | ~r3_orders_2(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3)) ) | (~spl3_20 | ~spl3_22)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k11_lattice3(X3,X4,X5) = X4 | ~r3_orders_2(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3)) ) | (~spl3_20 | ~spl3_22)),
% 0.21/0.53    inference(superposition,[],[f184,f161])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) ) | ~spl3_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f183])).
% 0.21/0.53  fof(f1110,plain,(
% 0.21/0.53    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_17 | ~spl3_28 | spl3_29 | ~spl3_52 | ~spl3_54),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1109])).
% 0.21/0.53  fof(f1109,plain,(
% 0.21/0.53    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_17 | ~spl3_28 | spl3_29 | ~spl3_52 | ~spl3_54)),
% 0.21/0.53    inference(subsumption_resolution,[],[f872,f1091])).
% 0.21/0.53  fof(f1091,plain,(
% 0.21/0.53    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_28 | ~spl3_52 | ~spl3_54)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f76,f543,f1065,f1088])).
% 0.21/0.53  fof(f1088,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) ) | ~spl3_54),
% 0.21/0.53    inference(avatar_component_clause,[],[f1087])).
% 0.21/0.53  fof(f1087,plain,(
% 0.21/0.53    spl3_54 <=> ! [X1,X0,X2] : (k11_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.53  fof(f1065,plain,(
% 0.21/0.53    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl3_52),
% 0.21/0.53    inference(avatar_component_clause,[],[f1063])).
% 0.21/0.53  fof(f1063,plain,(
% 0.21/0.53    spl3_52 <=> k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.53  fof(f872,plain,(
% 0.21/0.53    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (spl3_1 | ~spl3_3 | ~spl3_17 | ~spl3_28 | spl3_29)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f66,f76,f543,f862,f146])).
% 0.21/0.53  fof(f862,plain,(
% 0.21/0.53    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl3_29),
% 0.21/0.53    inference(avatar_component_clause,[],[f860])).
% 0.21/0.53  fof(f860,plain,(
% 0.21/0.53    spl3_29 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.53  fof(f1089,plain,(
% 0.21/0.53    spl3_54 | ~spl3_20 | ~spl3_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f187,f179,f160,f1087])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) ) | (~spl3_20 | ~spl3_21)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f186])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) ) | (~spl3_20 | ~spl3_21)),
% 0.21/0.53    inference(superposition,[],[f180,f161])).
% 0.21/0.53  fof(f1066,plain,(
% 0.21/0.53    spl3_52 | ~spl3_47 | ~spl3_51),
% 0.21/0.53    inference(avatar_split_clause,[],[f1061,f1057,f1015,f1063])).
% 0.21/0.53  fof(f1015,plain,(
% 0.21/0.53    spl3_47 <=> k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.53  fof(f1057,plain,(
% 0.21/0.53    spl3_51 <=> k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.54  fof(f1061,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_47 | ~spl3_51)),
% 0.21/0.54    inference(forward_demodulation,[],[f1059,f1017])).
% 0.21/0.54  fof(f1017,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl3_47),
% 0.21/0.54    inference(avatar_component_clause,[],[f1015])).
% 0.21/0.54  fof(f1059,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl3_51),
% 0.21/0.54    inference(avatar_component_clause,[],[f1057])).
% 0.21/0.54  fof(f1060,plain,(
% 0.21/0.54    spl3_51 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_19 | ~spl3_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f226,f195,f156,f105,f101,f97,f79,f74,f69,f1057])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    spl3_19 <=> ! [X1,X0,X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_19 | ~spl3_23)),
% 0.21/0.54    inference(forward_demodulation,[],[f200,f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_19)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f102,f71,f106,f76,f81,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) ) | ~spl3_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f156])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_23)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f102,f71,f106,f98,f76,f81,f76,f196])).
% 0.21/0.54  fof(f1018,plain,(
% 0.21/0.54    spl3_47 | ~spl3_32 | ~spl3_46),
% 0.21/0.54    inference(avatar_split_clause,[],[f1013,f1009,f881,f1015])).
% 0.21/0.54  fof(f881,plain,(
% 0.21/0.54    spl3_32 <=> sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.54  fof(f1009,plain,(
% 0.21/0.54    spl3_46 <=> k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.54  fof(f1013,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_32 | ~spl3_46)),
% 0.21/0.54    inference(forward_demodulation,[],[f1011,f883])).
% 0.21/0.54  fof(f883,plain,(
% 0.21/0.54    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) | ~spl3_32),
% 0.21/0.54    inference(avatar_component_clause,[],[f881])).
% 0.21/0.54  fof(f1011,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl3_46),
% 0.21/0.54    inference(avatar_component_clause,[],[f1009])).
% 0.21/0.54  fof(f1012,plain,(
% 0.21/0.54    spl3_46 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f202,f195,f105,f101,f97,f79,f74,f69,f1009])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_23)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f102,f71,f106,f98,f76,f76,f81,f196])).
% 0.21/0.54  fof(f884,plain,(
% 0.21/0.54    spl3_32 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_22 | ~spl3_24 | ~spl3_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f879,f875,f230,f183,f105,f101,f93,f74,f69,f881])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    spl3_24 <=> r3_orders_2(k2_yellow_1(sK0),sK1,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.54  fof(f875,plain,(
% 0.21/0.54    spl3_31 <=> k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.54  fof(f879,plain,(
% 0.21/0.54    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_22 | ~spl3_24 | ~spl3_31)),
% 0.21/0.54    inference(forward_demodulation,[],[f877,f869])).
% 0.21/0.54  fof(f869,plain,(
% 0.21/0.54    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_22 | ~spl3_24)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f94,f102,f71,f106,f76,f76,f232,f184])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),sK1,sK1) | ~spl3_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f230])).
% 0.21/0.54  fof(f877,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) | ~spl3_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f875])).
% 0.21/0.54  fof(f878,plain,(
% 0.21/0.54    spl3_31 | ~spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_10 | ~spl3_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f173,f160,f105,f101,f74,f69,f875])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_10 | ~spl3_20)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f102,f71,f106,f76,f76,f161])).
% 0.21/0.54  fof(f867,plain,(
% 0.21/0.54    ~spl3_29 | ~spl3_30 | spl3_5 | ~spl3_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f122,f119,f84,f864,f860])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl3_5 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl3_13 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (spl3_5 | ~spl3_13)),
% 0.21/0.54    inference(resolution,[],[f120,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) | spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f84])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    spl3_28 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f138,f124,f105,f79,f74,f541])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl3_14 <=> ! [X1,X0,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_14)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f76,f81,f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) ) | ~spl3_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  % (16963)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    spl3_24 | ~spl3_3 | ~spl3_7 | ~spl3_10 | ~spl3_15 | spl3_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f163,f132,f128,f105,f93,f74,f230])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),sK1,sK1) | (~spl3_3 | ~spl3_7 | ~spl3_10 | ~spl3_15 | spl3_16)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f94,f76,f76,f134,f129])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    spl3_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f58,f195])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    spl3_22),
% 0.21/0.54    inference(avatar_split_clause,[],[f56,f183])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    spl3_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f55,f179])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl3_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f60,f160])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl3_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f57,f156])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    spl3_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f145])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ~spl3_16 | ~spl3_2 | ~spl3_10 | ~spl3_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f116,f109,f105,f69,f132])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl3_11 <=> ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ~v2_struct_0(k2_yellow_1(sK0)) | (~spl3_2 | ~spl3_10 | ~spl3_11)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f71,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) ) | ~spl3_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f109])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl3_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f59,f128])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    spl3_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f61,f124])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl3_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f62,f119])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl3_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f109])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl3_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f105])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f101])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f97])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f93])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f84])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f79])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl3_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f74])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f69])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f64])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (16955)------------------------------
% 0.21/0.54  % (16955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16955)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (16955)Memory used [KB]: 7803
% 0.21/0.54  % (16955)Time elapsed: 0.086 s
% 0.21/0.54  % (16955)------------------------------
% 0.21/0.54  % (16955)------------------------------
% 0.21/0.54  % (16947)Success in time 0.182 s
%------------------------------------------------------------------------------
