%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1688+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 343 expanded)
%              Number of leaves         :   24 ( 131 expanded)
%              Depth                    :   21
%              Number of atoms          :  943 (2065 expanded)
%              Number of equality atoms :   31 ( 100 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f79,f83,f90,f94,f98,f102,f186,f190,f202,f206,f218,f222,f258])).

fof(f258,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f256,f78])).

fof(f78,plain,
    ( ~ v23_waybel_0(sK3,sK1,sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_8
  <=> v23_waybel_0(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f256,plain,
    ( v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f255,f217])).

fof(f217,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl6_19
  <=> v5_orders_3(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f255,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f254,f62])).

fof(f62,plain,
    ( l1_orders_2(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_4
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f254,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f253,f93])).

fof(f93,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_11
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f253,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f252,f205])).

fof(f205,plain,
    ( v5_orders_3(sK3,sK1,sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_18
  <=> v5_orders_3(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f252,plain,
    ( ~ v5_orders_3(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f251,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f251,plain,
    ( v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f250,f58])).

fof(f58,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f250,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f249,f101])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f248,f89])).

fof(f89,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_10
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f248,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f247,f70])).

fof(f70,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f247,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(resolution,[],[f231,f97])).

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(sK2,X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f230,f54])).

fof(f54,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(sK2,X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl6_1
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f229,f201])).

fof(f201,plain,
    ( v2_funct_1(sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_17
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_funct_1(sK3)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(sK2,X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl6_1
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f228,f50])).

fof(f50,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_funct_1(sK3)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(sK2,X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl6_20 ),
    inference(superposition,[],[f47,f221])).

fof(f221,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl6_20
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | k2_funct_1(X2) != X3
      | ~ v5_orders_3(X3,X1,X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X0) )
                 => ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) ) )
                & ~ ( ~ ( v23_waybel_0(X2,X0,X1)
                      <=> ( ? [X3] :
                              ( v5_orders_3(X3,X1,X0)
                              & k2_funct_1(X2) = X3
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                              & v1_funct_1(X3) )
                          & v5_orders_3(X2,X0,X1)
                          & v2_funct_1(X2) ) )
                    & ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d38_waybel_0)).

fof(f222,plain,
    ( spl6_20
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f198,f188,f184,f73,f53,f220])).

fof(f73,plain,
    ( spl6_7
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f184,plain,
    ( spl6_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f188,plain,
    ( spl6_16
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f198,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f197,f74])).

fof(f74,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f197,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl6_2
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f196,f185])).

fof(f185,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f196,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f192,f54])).

fof(f192,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl6_16 ),
    inference(resolution,[],[f189,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f189,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f218,plain,
    ( spl6_19
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f178,f100,f92,f81,f69,f65,f61,f57,f53,f216])).

fof(f81,plain,
    ( spl6_9
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f178,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f177,f82])).

fof(f82,plain,
    ( v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f177,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f176,f58])).

fof(f176,plain,
    ( v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f175,f66])).

fof(f175,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f174,f70])).

fof(f174,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f173,f93])).

fof(f173,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f172,f54])).

fof(f172,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f121,f62])).

fof(f121,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f101,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v5_orders_3(X2,X0,X1)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f206,plain,
    ( spl6_18
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f163,f100,f92,f81,f73,f69,f65,f61,f57,f53,f204])).

fof(f163,plain,
    ( v5_orders_3(sK3,sK1,sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f162,f155])).

fof(f155,plain,
    ( sK3 = sK5(sK0,sK1,sK2)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f154,f74])).

fof(f154,plain,
    ( k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f153,f82])).

fof(f153,plain,
    ( k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f152,f58])).

fof(f152,plain,
    ( v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f151,f66])).

fof(f151,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f150,f70])).

fof(f150,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f149,f93])).

fof(f149,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f148,f54])).

fof(f148,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f118,f62])).

fof(f118,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | k2_funct_1(X2) = sK5(X0,X1,X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f162,plain,
    ( v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f161,f82])).

fof(f161,plain,
    ( v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f160,f58])).

fof(f160,plain,
    ( v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f159,f66])).

fof(f159,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f158,f70])).

fof(f158,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f157,f93])).

fof(f157,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f156,f54])).

fof(f156,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f119,f62])).

fof(f119,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f101,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v5_orders_3(sK5(X0,X1,X2),X1,X0)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f202,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f195,f188,f184,f73,f53,f200])).

fof(f195,plain,
    ( v2_funct_1(sK3)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f194,f74])).

fof(f194,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl6_2
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f193,f185])).

fof(f193,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f191,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl6_16 ),
    inference(resolution,[],[f189,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f190,plain,
    ( spl6_16
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f170,f100,f92,f81,f69,f65,f61,f57,f53,f188])).

fof(f170,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f169,f82])).

fof(f169,plain,
    ( v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f168,f58])).

fof(f168,plain,
    ( v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f167,f66])).

fof(f167,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f166,f70])).

fof(f166,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f165,f93])).

fof(f165,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f164,f54])).

fof(f164,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f120,f62])).

fof(f120,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f101,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v2_funct_1(X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f186,plain,
    ( spl6_15
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f126,f100,f184])).

fof(f126,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_13 ),
    inference(resolution,[],[f101,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f102,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f23,f100])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( k2_funct_1(X2) = X3
                     => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_waybel_0)).

fof(f98,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f18,f96])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f22,f92])).

fof(f22,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f17,f88])).

fof(f17,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f83,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f24,f81])).

fof(f24,plain,(
    v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f20,f77])).

fof(f20,plain,(
    ~ v23_waybel_0(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f19,f73])).

fof(f19,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f16,f49])).

fof(f16,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
