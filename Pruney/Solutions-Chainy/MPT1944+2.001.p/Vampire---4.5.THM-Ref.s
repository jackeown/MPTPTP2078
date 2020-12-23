%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 387 expanded)
%              Number of leaves         :   44 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          : 1229 (2099 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f115,f119,f124,f128,f132,f140,f144,f151,f169,f174,f182,f196,f203,f207,f212,f216,f232,f244,f260,f296,f310,f336,f344])).

fof(f344,plain,
    ( ~ spl8_11
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f102,f199])).

fof(f199,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl8_30
  <=> ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f102,plain,
    ( ! [X0] : m1_subset_1(sK7(X0),X0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_11
  <=> ! [X0] : m1_subset_1(sK7(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f336,plain,
    ( spl8_45
    | ~ spl8_26
    | spl8_30
    | spl8_1
    | spl8_4
    | ~ spl8_8
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f318,f294,f130,f89,f73,f61,f198,f167,f291])).

fof(f291,plain,
    ( spl8_45
  <=> r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f167,plain,
    ( spl8_26
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f61,plain,
    ( spl8_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f73,plain,
    ( spl8_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f89,plain,
    ( spl8_8
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f130,plain,
    ( spl8_18
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
        | r1_waybel_0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f294,plain,
    ( spl8_46
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) )
    | spl8_1
    | spl8_4
    | ~ spl8_8
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f317,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f316,f90])).

fof(f90,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) )
    | spl8_1
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f315,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) )
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) )
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(resolution,[],[f295,f131])).

fof(f131,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | v2_struct_0(X0)
        | r1_waybel_0(X0,X1,X2) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f294])).

fof(f310,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | spl8_9
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_45 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | spl8_9
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f308,f94])).

fof(f94,plain,
    ( ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_9
  <=> r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f308,plain,
    ( r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f307,f74])).

fof(f307,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f306,f202])).

fof(f202,plain,
    ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl8_31
  <=> m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f306,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f305,f90])).

fof(f305,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f304,f70])).

fof(f70,plain,
    ( v7_waybel_0(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_3
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f304,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f303,f66])).

fof(f66,plain,
    ( v4_orders_2(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_2
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f303,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f302,f62])).

fof(f302,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f301,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f301,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f298,f78])).

fof(f78,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f298,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl8_29
    | ~ spl8_45 ),
    inference(resolution,[],[f292,f195])).

fof(f195,plain,
    ( ! [X0,X3,X1] :
        ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | v2_struct_0(X0)
        | r2_hidden(X3,k10_yellow_6(X0,X1)) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_29
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
        | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f292,plain,
    ( r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f291])).

fof(f296,plain,
    ( spl8_45
    | spl8_46
    | spl8_9
    | ~ spl8_31
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f271,f258,f214,f201,f93,f294,f291])).

fof(f214,plain,
    ( spl8_34
  <=> ! [X1,X2] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f258,plain,
    ( spl8_41
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | r2_hidden(X0,sK6(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | spl8_9
    | ~ spl8_31
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f270,f202])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | spl8_9
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f269,f94])).

fof(f269,plain,
    ( ! [X0] :
        ( r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(resolution,[],[f259,f215])).

fof(f215,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f214])).

fof(f259,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK6(sK0,sK1,X0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl8_41
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f253,f242,f122,f81,f77,f73,f258])).

fof(f122,plain,
    ( spl8_16
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,X0,X2)
        | r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f242,plain,
    ( spl8_39
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | r2_hidden(X0,sK6(sK0,sK1,X0)) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f252,f74])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | v2_struct_0(sK0)
        | r2_hidden(X0,sK6(sK0,sK1,X0)) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f251,f82])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,sK6(sK0,sK1,X0)) )
    | ~ spl8_5
    | ~ spl8_16
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f250,f78])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,sK6(sK0,sK1,X0)) )
    | ~ spl8_16
    | ~ spl8_39 ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,sK6(sK0,sK1,X0)) )
    | ~ spl8_16
    | ~ spl8_39 ),
    inference(resolution,[],[f243,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X1,X0,X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | r2_hidden(X2,X1) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f243,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( spl8_39
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f236,f230,f89,f81,f77,f73,f242])).

fof(f230,plain,
    ( spl8_37
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f235,f78])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f234,f74])).

fof(f234,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f233,f82])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl8_8
    | ~ spl8_37 ),
    inference(resolution,[],[f231,f90])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | r2_hidden(X1,k10_yellow_6(X0,sK1)) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,
    ( spl8_37
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f219,f210,f69,f65,f61,f230])).

fof(f210,plain,
    ( spl8_33
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
        | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | r2_hidden(X1,k10_yellow_6(X0,sK1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f218,f66])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | r2_hidden(X1,k10_yellow_6(X0,sK1)) )
    | spl8_1
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f217,f62])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | r2_hidden(X1,k10_yellow_6(X0,sK1)) )
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(resolution,[],[f211,f70])).

fof(f211,plain,
    ( ! [X0,X3,X1] :
        ( ~ v7_waybel_0(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
        | r2_hidden(X3,k10_yellow_6(X0,X1)) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f216,plain,
    ( ~ spl8_26
    | spl8_34
    | spl8_1
    | spl8_4
    | ~ spl8_8
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f192,f164,f138,f89,f73,f61,f214,f167])).

fof(f138,plain,
    ( spl8_20
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
        | r1_waybel_0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f164,plain,
    ( spl8_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f192,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1)
        | ~ m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1)) )
    | spl8_1
    | spl8_4
    | ~ spl8_8
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f191,f74])).

fof(f191,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,X1)
        | ~ m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1)) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f190,f90])).

fof(f190,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,X1)
        | ~ m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1)) )
    | spl8_1
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f185,f62])).

fof(f185,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,X1)
        | ~ m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1)) )
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(superposition,[],[f139,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f164])).

fof(f139,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | v2_struct_0(X0)
        | r1_waybel_0(X0,X1,X2) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f138])).

fof(f212,plain,
    ( spl8_33
    | ~ spl8_17
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f208,f205,f126,f210])).

fof(f126,plain,
    ( spl8_17
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f205,plain,
    ( spl8_32
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
        | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f208,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
        | r2_hidden(X3,k10_yellow_6(X0,X1)) )
    | ~ spl8_17
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f206,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X0) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f206,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
        | r2_hidden(X3,k10_yellow_6(X0,X1)) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,(
    spl8_32 ),
    inference(avatar_split_clause,[],[f58,f205])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
      | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
      | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
      | r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f203,plain,
    ( spl8_30
    | ~ spl8_26
    | spl8_31
    | spl8_1
    | spl8_4
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f189,f164,f113,f89,f73,f61,f201,f167,f198])).

fof(f113,plain,
    ( spl8_14
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f189,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | spl8_1
    | spl8_4
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f188,f74])).

fof(f188,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f187,f90])).

fof(f187,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | spl8_1
    | ~ spl8_14
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f186,f62])).

fof(f186,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl8_14
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_14
    | ~ spl8_25 ),
    inference(superposition,[],[f114,f165])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | v2_struct_0(X0) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f196,plain,
    ( spl8_29
    | ~ spl8_17
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f183,f180,f126,f194])).

fof(f180,plain,
    ( spl8_28
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
        | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f183,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
        | r2_hidden(X3,k10_yellow_6(X0,X1)) )
    | ~ spl8_17
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f181,f127])).

fof(f181,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
        | r2_hidden(X3,k10_yellow_6(X0,X1)) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,(
    spl8_28 ),
    inference(avatar_split_clause,[],[f57,f180])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
      | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
      | r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f174,plain,
    ( ~ spl8_6
    | ~ spl8_10
    | spl8_26 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_10
    | spl8_26 ),
    inference(subsumption_resolution,[],[f171,f82])).

fof(f171,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_10
    | spl8_26 ),
    inference(resolution,[],[f168,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_10
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f168,plain,
    ( ~ l1_struct_0(sK0)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( spl8_25
    | ~ spl8_26
    | spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f158,f149,f89,f85,f73,f167,f164])).

fof(f85,plain,
    ( spl8_7
  <=> v1_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f149,plain,
    ( spl8_22
  <=> ! [X1,X0] :
        ( ~ l1_struct_0(X0)
        | v2_struct_0(X0)
        | ~ v1_yellow_6(sK1,X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) )
    | spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f157,f90])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) )
    | spl8_4
    | ~ spl8_7
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f156,f74])).

fof(f156,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) )
    | ~ spl8_7
    | ~ spl8_22 ),
    inference(resolution,[],[f150,f86])).

fof(f86,plain,
    ( v1_yellow_6(sK1,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ v1_yellow_6(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl8_22
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f147,f142,f69,f65,f61,f149])).

fof(f142,plain,
    ( spl8_21
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v1_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | v2_struct_0(X0)
        | ~ v1_yellow_6(sK1,X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f146,f66])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X0)
        | ~ v1_yellow_6(sK1,X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1) )
    | spl8_1
    | ~ spl8_3
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f145,f62])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X0)
        | ~ v1_yellow_6(sK1,X0)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1) )
    | ~ spl8_3
    | ~ spl8_21 ),
    inference(resolution,[],[f143,f70])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X0)
        | ~ v1_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f39,f142])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v1_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f140,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f42,f138])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f132,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f40,f130])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f54,f126])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f124,plain,
    ( spl8_16
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f120,f117,f105,f122])).

fof(f105,plain,
    ( spl8_12
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f117,plain,
    ( spl8_15
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,X0,X2)
        | r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,X0,X2)
        | r2_hidden(X2,X1) )
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f118,f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,X0,X2)
        | r2_hidden(X2,X1) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f45,f117])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f115,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f56,f113])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(f107,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f55,f105])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f103,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f99,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f95,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f34,f93])).

fof(f34,plain,(
    ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f91,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (32597)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.45  % (32597)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % (32589)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.45  % (32589)Refutation not found, incomplete strategy% (32589)------------------------------
% 0.21/0.45  % (32589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (32589)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (32589)Memory used [KB]: 10618
% 0.21/0.45  % (32589)Time elapsed: 0.065 s
% 0.21/0.45  % (32589)------------------------------
% 0.21/0.45  % (32589)------------------------------
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f348,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f115,f119,f124,f128,f132,f140,f144,f151,f169,f174,f182,f196,f203,f207,f212,f216,f232,f244,f260,f296,f310,f336,f344])).
% 0.21/0.45  fof(f344,plain,(
% 0.21/0.45    ~spl8_11 | ~spl8_30),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.45  fof(f337,plain,(
% 0.21/0.45    $false | (~spl8_11 | ~spl8_30)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f102,f199])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl8_30),
% 0.21/0.45    inference(avatar_component_clause,[],[f198])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    spl8_30 <=> ! [X0] : ~m1_subset_1(X0,u1_struct_0(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) ) | ~spl8_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    spl8_11 <=> ! [X0] : m1_subset_1(sK7(X0),X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.45  fof(f336,plain,(
% 0.21/0.45    spl8_45 | ~spl8_26 | spl8_30 | spl8_1 | spl8_4 | ~spl8_8 | ~spl8_18 | ~spl8_46),
% 0.21/0.45    inference(avatar_split_clause,[],[f318,f294,f130,f89,f73,f61,f198,f167,f291])).
% 0.21/0.45  fof(f291,plain,(
% 0.21/0.45    spl8_45 <=> r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.21/0.45  fof(f167,plain,(
% 0.21/0.45    spl8_26 <=> l1_struct_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl8_1 <=> v2_struct_0(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl8_4 <=> v2_struct_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl8_8 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    spl8_18 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.45  fof(f294,plain,(
% 0.21/0.45    spl8_46 <=> ! [X0] : (~m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.21/0.45  fof(f318,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))) ) | (spl8_1 | spl8_4 | ~spl8_8 | ~spl8_18 | ~spl8_46)),
% 0.21/0.45    inference(subsumption_resolution,[],[f317,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ~v2_struct_0(sK0) | spl8_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f73])).
% 0.21/0.45  fof(f317,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))) ) | (spl8_1 | ~spl8_8 | ~spl8_18 | ~spl8_46)),
% 0.21/0.45    inference(subsumption_resolution,[],[f316,f90])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    l1_waybel_0(sK1,sK0) | ~spl8_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f89])).
% 0.21/0.45  fof(f316,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))) ) | (spl8_1 | ~spl8_18 | ~spl8_46)),
% 0.21/0.45    inference(subsumption_resolution,[],[f315,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ~v2_struct_0(sK1) | spl8_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f315,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))) ) | (~spl8_18 | ~spl8_46)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f314])).
% 0.21/0.45  fof(f314,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))) ) | (~spl8_18 | ~spl8_46)),
% 0.21/0.45    inference(resolution,[],[f295,f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) ) | ~spl8_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f130])).
% 0.21/0.45  fof(f295,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl8_46),
% 0.21/0.45    inference(avatar_component_clause,[],[f294])).
% 0.21/0.45  fof(f310,plain,(
% 0.21/0.45    spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | spl8_9 | ~spl8_29 | ~spl8_31 | ~spl8_45),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.45  fof(f309,plain,(
% 0.21/0.45    $false | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | spl8_9 | ~spl8_29 | ~spl8_31 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f308,f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ~r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | spl8_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    spl8_9 <=> r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.45  fof(f308,plain,(
% 0.21/0.45    r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_29 | ~spl8_31 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f307,f74])).
% 0.21/0.45  fof(f307,plain,(
% 0.21/0.45    v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_29 | ~spl8_31 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f306,f202])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~spl8_31),
% 0.21/0.45    inference(avatar_component_clause,[],[f201])).
% 0.21/0.45  fof(f201,plain,(
% 0.21/0.45    spl8_31 <=> m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.45  fof(f306,plain,(
% 0.21/0.45    ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f305,f90])).
% 0.21/0.45  fof(f305,plain,(
% 0.21/0.45    ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f304,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    v7_waybel_0(sK1) | ~spl8_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl8_3 <=> v7_waybel_0(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.45  fof(f304,plain,(
% 0.21/0.45    ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (spl8_1 | ~spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f303,f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    v4_orders_2(sK1) | ~spl8_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl8_2 <=> v4_orders_2(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.45  fof(f303,plain,(
% 0.21/0.45    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (spl8_1 | ~spl8_5 | ~spl8_6 | ~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f302,f62])).
% 0.21/0.45  fof(f302,plain,(
% 0.21/0.45    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (~spl8_5 | ~spl8_6 | ~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f301,f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    l1_pre_topc(sK0) | ~spl8_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl8_6 <=> l1_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.45  fof(f301,plain,(
% 0.21/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (~spl8_5 | ~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(subsumption_resolution,[],[f298,f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    v2_pre_topc(sK0) | ~spl8_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f77])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl8_5 <=> v2_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.45  fof(f298,plain,(
% 0.21/0.45    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | (~spl8_29 | ~spl8_45)),
% 0.21/0.45    inference(resolution,[],[f292,f195])).
% 0.21/0.45  fof(f195,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X3,k10_yellow_6(X0,X1))) ) | ~spl8_29),
% 0.21/0.45    inference(avatar_component_clause,[],[f194])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    spl8_29 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | r2_hidden(X3,k10_yellow_6(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.45  fof(f292,plain,(
% 0.21/0.45    r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) | ~spl8_45),
% 0.21/0.45    inference(avatar_component_clause,[],[f291])).
% 0.21/0.45  fof(f296,plain,(
% 0.21/0.45    spl8_45 | spl8_46 | spl8_9 | ~spl8_31 | ~spl8_34 | ~spl8_41),
% 0.21/0.45    inference(avatar_split_clause,[],[f271,f258,f214,f201,f93,f294,f291])).
% 0.21/0.45  fof(f214,plain,(
% 0.21/0.45    spl8_34 <=> ! [X1,X2] : (~r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(X2,u1_struct_0(sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.45  fof(f258,plain,(
% 0.21/0.45    spl8_41 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | r2_hidden(X0,sK6(sK0,sK1,X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.21/0.45  fof(f271,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (spl8_9 | ~spl8_31 | ~spl8_34 | ~spl8_41)),
% 0.21/0.45    inference(subsumption_resolution,[],[f270,f202])).
% 0.21/0.45  fof(f270,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (spl8_9 | ~spl8_34 | ~spl8_41)),
% 0.21/0.45    inference(subsumption_resolution,[],[f269,f94])).
% 0.21/0.45  fof(f269,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_34 | ~spl8_41)),
% 0.21/0.45    inference(resolution,[],[f259,f215])).
% 0.21/0.45  fof(f215,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(X2,u1_struct_0(sK1))) ) | ~spl8_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f214])).
% 0.21/0.45  fof(f259,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(X0,sK6(sK0,sK1,X0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_41),
% 0.21/0.45    inference(avatar_component_clause,[],[f258])).
% 0.21/0.45  fof(f260,plain,(
% 0.21/0.45    spl8_41 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_16 | ~spl8_39),
% 0.21/0.45    inference(avatar_split_clause,[],[f253,f242,f122,f81,f77,f73,f258])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    spl8_16 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    spl8_39 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.21/0.45  fof(f253,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | r2_hidden(X0,sK6(sK0,sK1,X0))) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_16 | ~spl8_39)),
% 0.21/0.45    inference(subsumption_resolution,[],[f252,f74])).
% 0.21/0.45  fof(f252,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK0) | r2_hidden(X0,sK6(sK0,sK1,X0))) ) | (~spl8_5 | ~spl8_6 | ~spl8_16 | ~spl8_39)),
% 0.21/0.45    inference(subsumption_resolution,[],[f251,f82])).
% 0.21/0.45  fof(f251,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,sK6(sK0,sK1,X0))) ) | (~spl8_5 | ~spl8_16 | ~spl8_39)),
% 0.21/0.45    inference(subsumption_resolution,[],[f250,f78])).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,sK6(sK0,sK1,X0))) ) | (~spl8_16 | ~spl8_39)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f249])).
% 0.21/0.45  fof(f249,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,sK6(sK0,sK1,X0))) ) | (~spl8_16 | ~spl8_39)),
% 0.21/0.45    inference(resolution,[],[f243,f123])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,X1)) ) | ~spl8_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f122])).
% 0.21/0.45  fof(f243,plain,(
% 0.21/0.45    ( ! [X0] : (m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1))) ) | ~spl8_39),
% 0.21/0.45    inference(avatar_component_clause,[],[f242])).
% 0.21/0.45  fof(f244,plain,(
% 0.21/0.45    spl8_39 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_37),
% 0.21/0.45    inference(avatar_split_clause,[],[f236,f230,f89,f81,f77,f73,f242])).
% 0.21/0.45  fof(f230,plain,(
% 0.21/0.45    spl8_37 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,sK1,X1),X0,X1) | r2_hidden(X1,k10_yellow_6(X0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.45  fof(f236,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1))) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_37)),
% 0.21/0.45    inference(subsumption_resolution,[],[f235,f78])).
% 0.21/0.45  fof(f235,plain,(
% 0.21/0.45    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1))) ) | (spl8_4 | ~spl8_6 | ~spl8_8 | ~spl8_37)),
% 0.21/0.45    inference(subsumption_resolution,[],[f234,f74])).
% 0.21/0.45  fof(f234,plain,(
% 0.21/0.45    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1))) ) | (~spl8_6 | ~spl8_8 | ~spl8_37)),
% 0.21/0.45    inference(subsumption_resolution,[],[f233,f82])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1))) ) | (~spl8_8 | ~spl8_37)),
% 0.21/0.45    inference(resolution,[],[f231,f90])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_waybel_0(sK1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,sK1,X1),X0,X1) | r2_hidden(X1,k10_yellow_6(X0,sK1))) ) | ~spl8_37),
% 0.21/0.45    inference(avatar_component_clause,[],[f230])).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    spl8_37 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_33),
% 0.21/0.45    inference(avatar_split_clause,[],[f219,f210,f69,f65,f61,f230])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    spl8_33 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,k10_yellow_6(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.45  fof(f219,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,sK1,X1),X0,X1) | r2_hidden(X1,k10_yellow_6(X0,sK1))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_33)),
% 0.21/0.45    inference(subsumption_resolution,[],[f218,f66])).
% 0.21/0.45  fof(f218,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v4_orders_2(sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,sK1,X1),X0,X1) | r2_hidden(X1,k10_yellow_6(X0,sK1))) ) | (spl8_1 | ~spl8_3 | ~spl8_33)),
% 0.21/0.45    inference(subsumption_resolution,[],[f217,f62])).
% 0.21/0.45  fof(f217,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,sK1,X1),X0,X1) | r2_hidden(X1,k10_yellow_6(X0,sK1))) ) | (~spl8_3 | ~spl8_33)),
% 0.21/0.45    inference(resolution,[],[f211,f70])).
% 0.21/0.45  fof(f211,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~v7_waybel_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,k10_yellow_6(X0,X1))) ) | ~spl8_33),
% 0.21/0.45    inference(avatar_component_clause,[],[f210])).
% 0.21/0.45  fof(f216,plain,(
% 0.21/0.45    ~spl8_26 | spl8_34 | spl8_1 | spl8_4 | ~spl8_8 | ~spl8_20 | ~spl8_25),
% 0.21/0.45    inference(avatar_split_clause,[],[f192,f164,f138,f89,f73,f61,f214,f167])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    spl8_20 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | r1_waybel_0(X0,X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    spl8_25 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1))) ) | (spl8_1 | spl8_4 | ~spl8_8 | ~spl8_20 | ~spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f191,f74])).
% 0.21/0.45  fof(f191,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1))) ) | (spl8_1 | ~spl8_8 | ~spl8_20 | ~spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f190,f90])).
% 0.21/0.45  fof(f190,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1))) ) | (spl8_1 | ~spl8_20 | ~spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f185,f62])).
% 0.21/0.45  fof(f185,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(sK3(sK0,sK1,X1,X2),u1_struct_0(sK1))) ) | (~spl8_20 | ~spl8_25)),
% 0.21/0.45    inference(superposition,[],[f139,f165])).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    ( ! [X0] : (k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl8_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f164])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) ) | ~spl8_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f138])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    spl8_33 | ~spl8_17 | ~spl8_32),
% 0.21/0.45    inference(avatar_split_clause,[],[f208,f205,f126,f210])).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    spl8_17 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    spl8_32 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,k10_yellow_6(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,k10_yellow_6(X0,X1))) ) | (~spl8_17 | ~spl8_32)),
% 0.21/0.45    inference(subsumption_resolution,[],[f206,f127])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) ) | ~spl8_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f126])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,k10_yellow_6(X0,X1))) ) | ~spl8_32),
% 0.21/0.45    inference(avatar_component_clause,[],[f205])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    spl8_32),
% 0.21/0.45    inference(avatar_split_clause,[],[f58,f205])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,k10_yellow_6(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,X3),X0,X3) | r2_hidden(X3,X2) | k10_yellow_6(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    spl8_30 | ~spl8_26 | spl8_31 | spl8_1 | spl8_4 | ~spl8_8 | ~spl8_14 | ~spl8_25),
% 0.21/0.45    inference(avatar_split_clause,[],[f189,f164,f113,f89,f73,f61,f201,f167,f198])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    spl8_14 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.45  fof(f189,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (spl8_1 | spl8_4 | ~spl8_8 | ~spl8_14 | ~spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f188,f74])).
% 0.21/0.45  fof(f188,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0)) ) | (spl8_1 | ~spl8_8 | ~spl8_14 | ~spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f187,f90])).
% 0.21/0.45  fof(f187,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0)) ) | (spl8_1 | ~spl8_14 | ~spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f186,f62])).
% 0.21/0.45  fof(f186,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0)) ) | (~spl8_14 | ~spl8_25)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f184])).
% 0.21/0.45  fof(f184,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_14 | ~spl8_25)),
% 0.21/0.45    inference(superposition,[],[f114,f165])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0)) ) | ~spl8_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f113])).
% 0.21/0.45  fof(f196,plain,(
% 0.21/0.45    spl8_29 | ~spl8_17 | ~spl8_28),
% 0.21/0.45    inference(avatar_split_clause,[],[f183,f180,f126,f194])).
% 0.21/0.45  fof(f180,plain,(
% 0.21/0.45    spl8_28 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | r2_hidden(X3,k10_yellow_6(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.45  fof(f183,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | r2_hidden(X3,k10_yellow_6(X0,X1))) ) | (~spl8_17 | ~spl8_28)),
% 0.21/0.45    inference(subsumption_resolution,[],[f181,f127])).
% 0.21/0.45  fof(f181,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | r2_hidden(X3,k10_yellow_6(X0,X1))) ) | ~spl8_28),
% 0.21/0.45    inference(avatar_component_clause,[],[f180])).
% 0.21/0.45  fof(f182,plain,(
% 0.21/0.45    spl8_28),
% 0.21/0.45    inference(avatar_split_clause,[],[f57,f180])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | r2_hidden(X3,k10_yellow_6(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X3)) | r2_hidden(X3,X2) | k10_yellow_6(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f174,plain,(
% 0.21/0.45    ~spl8_6 | ~spl8_10 | spl8_26),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f173])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    $false | (~spl8_6 | ~spl8_10 | spl8_26)),
% 0.21/0.45    inference(subsumption_resolution,[],[f171,f82])).
% 0.21/0.45  fof(f171,plain,(
% 0.21/0.45    ~l1_pre_topc(sK0) | (~spl8_10 | spl8_26)),
% 0.21/0.45    inference(resolution,[],[f168,f98])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl8_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl8_10 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.45  fof(f168,plain,(
% 0.21/0.45    ~l1_struct_0(sK0) | spl8_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f167])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    spl8_25 | ~spl8_26 | spl8_4 | ~spl8_7 | ~spl8_8 | ~spl8_22),
% 0.21/0.45    inference(avatar_split_clause,[],[f158,f149,f89,f85,f73,f167,f164])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl8_7 <=> v1_yellow_6(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.45  fof(f149,plain,(
% 0.21/0.45    spl8_22 <=> ! [X1,X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.45  fof(f158,plain,(
% 0.21/0.45    ( ! [X0] : (~l1_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)) ) | (spl8_4 | ~spl8_7 | ~spl8_8 | ~spl8_22)),
% 0.21/0.45    inference(subsumption_resolution,[],[f157,f90])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    ( ! [X0] : (~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)) ) | (spl8_4 | ~spl8_7 | ~spl8_22)),
% 0.21/0.45    inference(subsumption_resolution,[],[f156,f74])).
% 0.21/0.45  fof(f156,plain,(
% 0.21/0.45    ( ! [X0] : (v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)) ) | (~spl8_7 | ~spl8_22)),
% 0.21/0.45    inference(resolution,[],[f150,f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    v1_yellow_6(sK1,sK0) | ~spl8_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_yellow_6(sK1,X0) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1)) ) | ~spl8_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f149])).
% 0.21/0.45  fof(f151,plain,(
% 0.21/0.45    spl8_22 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f147,f142,f69,f65,f61,f149])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    spl8_21 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v1_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_21)),
% 0.21/0.45    inference(subsumption_resolution,[],[f146,f66])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_struct_0(X0) | ~v4_orders_2(sK1) | v2_struct_0(X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1)) ) | (spl8_1 | ~spl8_3 | ~spl8_21)),
% 0.21/0.45    inference(subsumption_resolution,[],[f145,f62])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_struct_0(X0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | k2_waybel_0(X0,sK1,X1) = k4_yellow_6(X0,sK1)) ) | (~spl8_3 | ~spl8_21)),
% 0.21/0.45    inference(resolution,[],[f143,f70])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~v1_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)) ) | ~spl8_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f142])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    spl8_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f142])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v1_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_6)).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    spl8_20),
% 0.21/0.45    inference(avatar_split_clause,[],[f42,f138])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | r1_waybel_0(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    spl8_18),
% 0.21/0.45    inference(avatar_split_clause,[],[f40,f130])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    spl8_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f54,f126])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    spl8_16 | ~spl8_12 | ~spl8_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f120,f117,f105,f122])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    spl8_12 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    spl8_15 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) ) | (~spl8_12 | ~spl8_15)),
% 0.21/0.45    inference(subsumption_resolution,[],[f118,f106])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl8_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f105])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) ) | ~spl8_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f117])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    spl8_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f45,f117])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    spl8_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f56,f113])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    spl8_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f55,f105])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl8_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f53,f101])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl8_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f97])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ~spl8_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f93])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ~r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl8_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f89])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    l1_waybel_0(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl8_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f85])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v1_yellow_6(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl8_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f81])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl8_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f77])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ~spl8_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f73])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl8_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f69])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    v7_waybel_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl8_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f65])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v4_orders_2(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~spl8_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f61])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ~v2_struct_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (32597)------------------------------
% 0.21/0.46  % (32597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (32597)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (32597)Memory used [KB]: 10874
% 0.21/0.46  % (32597)Time elapsed: 0.064 s
% 0.21/0.46  % (32597)------------------------------
% 0.21/0.46  % (32597)------------------------------
% 0.21/0.46  % (32587)Success in time 0.099 s
%------------------------------------------------------------------------------
