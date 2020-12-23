%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:38 EST 2020

% Result     : Theorem 3.38s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  391 ( 991 expanded)
%              Number of leaves         :   51 ( 378 expanded)
%              Depth                    :   47
%              Number of atoms          : 2726 (5124 expanded)
%              Number of equality atoms :   71 (  94 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f121,f136,f141,f146,f151,f155,f159,f178,f187,f196,f203,f211,f222,f254,f273,f284,f293,f304,f312,f354,f378,f491,f718,f1041,f1166,f1239,f1455,f1527,f1540,f1726,f2106,f2125,f2366,f2387])).

fof(f2387,plain,
    ( ~ spl7_8
    | spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_44
    | spl7_128 ),
    inference(avatar_contradiction_clause,[],[f2386])).

fof(f2386,plain,
    ( $false
    | ~ spl7_8
    | spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_44
    | spl7_128 ),
    inference(subsumption_resolution,[],[f2385,f176])).

fof(f176,plain,
    ( v4_orders_2(sK3(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_15
  <=> v4_orders_2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f2385,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | ~ spl7_8
    | spl7_12
    | ~ spl7_14
    | ~ spl7_44
    | spl7_128 ),
    inference(subsumption_resolution,[],[f2384,f172])).

fof(f172,plain,
    ( v7_waybel_0(sK3(sK0))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_14
  <=> v7_waybel_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f2384,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ spl7_8
    | spl7_12
    | ~ spl7_44
    | spl7_128 ),
    inference(subsumption_resolution,[],[f2383,f145])).

fof(f145,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl7_8
  <=> l1_waybel_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f2383,plain,
    ( ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | spl7_12
    | ~ spl7_44
    | spl7_128 ),
    inference(subsumption_resolution,[],[f2381,f165])).

fof(f165,plain,
    ( ~ v2_struct_0(sK3(sK0))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl7_12
  <=> v2_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f2381,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ spl7_44
    | spl7_128 ),
    inference(resolution,[],[f2365,f717])).

fof(f717,plain,
    ( ! [X1] :
        ( v3_yellow_6(sK2(X1),sK0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl7_44
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | v3_yellow_6(sK2(X1),sK0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f2365,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl7_128 ),
    inference(avatar_component_clause,[],[f2363])).

fof(f2363,plain,
    ( spl7_128
  <=> v3_yellow_6(sK2(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f2366,plain,
    ( ~ spl7_128
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f2359,f1236,f248,f244,f240,f236,f91,f86,f81,f2363])).

fof(f81,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f86,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f91,plain,
    ( spl7_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f236,plain,
    ( spl7_18
  <=> v2_struct_0(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f240,plain,
    ( spl7_19
  <=> l1_waybel_0(sK2(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f244,plain,
    ( spl7_20
  <=> v7_waybel_0(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f248,plain,
    ( spl7_21
  <=> v4_orders_2(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f1236,plain,
    ( spl7_74
  <=> k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f2359,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2358,f83])).

fof(f83,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f2358,plain,
    ( v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2357,f241])).

fof(f241,plain,
    ( l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f2357,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2356,f245])).

fof(f245,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f2356,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2355,f249])).

fof(f249,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f248])).

fof(f2355,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2354,f237])).

fof(f237,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f236])).

fof(f2354,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2353,f93])).

fof(f93,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f2353,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_2
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f2352,f88])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f2352,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_74 ),
    inference(trivial_inequality_removal,[],[f2351])).

fof(f2351,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_74 ),
    inference(superposition,[],[f58,f1238])).

fof(f1238,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ v3_yellow_6(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f2125,plain,(
    ~ spl7_37 ),
    inference(avatar_contradiction_clause,[],[f2124])).

fof(f2124,plain,
    ( $false
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f2117,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2117,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_37 ),
    inference(resolution,[],[f490,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f490,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl7_37
  <=> r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f2106,plain,
    ( spl7_74
    | ~ spl7_36
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f2028,f1448,f485,f1236])).

fof(f485,plain,
    ( spl7_36
  <=> ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1448,plain,
    ( spl7_84
  <=> r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f2028,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))
    | ~ spl7_36
    | ~ spl7_84 ),
    inference(resolution,[],[f1450,f497])).

fof(f497,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl7_36 ),
    inference(resolution,[],[f486,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f486,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f485])).

fof(f1450,plain,
    ( r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f1448])).

fof(f1726,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24
    | spl7_67 ),
    inference(avatar_contradiction_clause,[],[f1725])).

fof(f1725,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24
    | spl7_67 ),
    inference(subsumption_resolution,[],[f1713,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1713,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(sK0,sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24
    | spl7_67 ),
    inference(backward_demodulation,[],[f1165,f1707])).

fof(f1707,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1706,f150])).

fof(f150,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl7_9
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1706,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_waybel_0(sK1,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1705,f140])).

fof(f140,plain,
    ( v7_waybel_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_7
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1705,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1704,f135])).

fof(f135,plain,
    ( v4_orders_2(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_6
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1704,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1703,f120])).

fof(f120,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1703,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f1700])).

fof(f1700,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_24 ),
    inference(resolution,[],[f1188,f158])).

fof(f158,plain,
    ( ! [X10] :
        ( r3_waybel_9(sK0,X10,sK4(sK0,X10))
        | v2_struct_0(X10)
        | ~ l1_waybel_0(X10,sK0)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_11
  <=> ! [X10] :
        ( v2_struct_0(X10)
        | r3_waybel_9(sK0,X10,sK4(sK0,X10))
        | ~ l1_waybel_0(X10,sK0)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1188,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2)))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1187,f115])).

fof(f115,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_4
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1187,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2)))
        | ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1186,f83])).

fof(f1186,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2)))
        | ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | v2_struct_0(sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1185,f93])).

fof(f1185,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2)))
        | ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | v2_struct_0(sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1184,f88])).

fof(f1184,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2)))
        | ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | v2_struct_0(sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(resolution,[],[f1105,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f1105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1104,f83])).

fof(f1104,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1103,f150])).

fof(f1103,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1102,f140])).

fof(f1102,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1101,f135])).

fof(f1101,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1100,f120])).

fof(f1100,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f1099,f265])).

fof(f265,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl7_24
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1099,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f1098])).

fof(f1098,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(resolution,[],[f951,f104])).

fof(f104,plain,
    ( ! [X4,X3] :
        ( m2_yellow_6(sK5(sK0,X3,X4),sK0,X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X3,X4)
        | v2_struct_0(X3) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f103,f93])).

fof(f103,plain,
    ( ! [X4,X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X3,X4)
        | m2_yellow_6(sK5(sK0,X3,X4),sK0,X3) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f96,f83])).

fof(f96,plain,
    ( ! [X4,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X3,X4)
        | m2_yellow_6(sK5(sK0,X3,X4),sK0,X3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f951,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_yellow_6(sK5(sK0,sK1,X0),X1,X2)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f950,f150])).

fof(f950,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,X1)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X1,X2)
        | v2_struct_0(X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f949,f140])).

fof(f949,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,X1)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X1,X2)
        | v2_struct_0(X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f948,f135])).

fof(f948,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,X1)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X1,X2)
        | v2_struct_0(X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f947,f120])).

fof(f947,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,X1)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X1,X2)
        | v2_struct_0(X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f946])).

fof(f946,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,X1)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X1,X2)
        | v2_struct_0(X1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(resolution,[],[f836,f104])).

fof(f836,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | ~ l1_struct_0(X2)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,X2)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X2,X3)
        | v2_struct_0(X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f835,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f835,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1)
        | ~ l1_struct_0(X2)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,X2)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X2,X3)
        | v2_struct_0(X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f834,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f834,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v4_orders_2(sK5(sK0,sK1,X0))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1)
        | ~ l1_struct_0(X2)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,X2)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),X2,X3)
        | v2_struct_0(X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(resolution,[],[f784,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f784,plain,
    ( ! [X0,X1] :
        ( ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f783,f83])).

fof(f783,plain,
    ( ! [X0,X1] :
        ( ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f782,f265])).

fof(f782,plain,
    ( ! [X0,X1] :
        ( ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(resolution,[],[f746,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f746,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f745,f120])).

fof(f745,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f744,f150])).

fof(f744,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f743,f140])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f742,f135])).

fof(f742,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(resolution,[],[f712,f104])).

fof(f712,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(X0,sK0,sK1)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,X0)
        | v2_struct_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(resolution,[],[f154,f110])).

fof(f110,plain,
    ( ! [X9] :
        ( v3_yellow_6(X9,sK0)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,X9)
        | v2_struct_0(X9) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f109,f93])).

fof(f109,plain,
    ( ! [X9] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,X9)
        | v3_yellow_6(X9,sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f99,f83])).

fof(f99,plain,
    ( ! [X9] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,sK0)
        | k1_xboole_0 = k10_yellow_6(sK0,X9)
        | v3_yellow_6(X9,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | k1_xboole_0 = k10_yellow_6(X0,X1)
      | v3_yellow_6(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f154,plain,
    ( ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_10
  <=> ! [X2] :
        ( ~ m2_yellow_6(X2,sK0,sK1)
        | ~ v3_yellow_6(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1165,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),k1_zfmisc_1(sK4(sK0,sK1)))
    | spl7_67 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1163,plain,
    ( spl7_67
  <=> m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),k1_zfmisc_1(sK4(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f1540,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | spl7_93 ),
    inference(avatar_contradiction_clause,[],[f1539])).

fof(f1539,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1538,f83])).

fof(f1538,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1537,f241])).

fof(f1537,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_20
    | ~ spl7_21
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1536,f245])).

fof(f1536,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_21
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1535,f249])).

fof(f1535,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1534,f237])).

fof(f1534,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1533,f93])).

fof(f1533,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | spl7_93 ),
    inference(subsumption_resolution,[],[f1530,f88])).

fof(f1530,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v2_struct_0(sK0)
    | spl7_93 ),
    inference(resolution,[],[f1526,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f1526,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_93 ),
    inference(avatar_component_clause,[],[f1524])).

fof(f1524,plain,
    ( spl7_93
  <=> m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f1527,plain,
    ( ~ spl7_93
    | spl7_85 ),
    inference(avatar_split_clause,[],[f1471,f1452,f1524])).

fof(f1452,plain,
    ( spl7_85
  <=> r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1471,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_85 ),
    inference(resolution,[],[f1454,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1454,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),u1_struct_0(sK0))
    | spl7_85 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1455,plain,
    ( spl7_84
    | ~ spl7_85
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f1271,f1233,f1452,f1448])).

fof(f1233,plain,
    ( spl7_73
  <=> ! [X2] :
        ( ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f1271,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),u1_struct_0(sK0))
    | r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)
    | ~ spl7_73 ),
    inference(resolution,[],[f1240,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl7_73 ),
    inference(resolution,[],[f1234,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1234,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2) )
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f1233])).

fof(f1239,plain,
    ( spl7_73
    | spl7_74
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f465,f348,f252,f1236,f1233])).

fof(f252,plain,
    ( spl7_22
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f348,plain,
    ( spl7_26
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0)))
        | k10_yellow_6(sK0,sK3(sK0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f465,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))
        | ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f453,f438])).

fof(f438,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK3(sK0))
    | ~ spl7_26 ),
    inference(resolution,[],[f383,f48])).

fof(f383,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k10_yellow_6(sK0,sK3(sK0))))
        | k10_yellow_6(sK0,sK3(sK0)) = X0 )
    | ~ spl7_26 ),
    inference(resolution,[],[f349,f75])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0)))
        | k10_yellow_6(sK0,sK3(sK0)) = X0 )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f348])).

fof(f453,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2)
        | k10_yellow_6(sK0,sK3(sK0)) = k10_yellow_6(sK0,sK2(sK3(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(backward_demodulation,[],[f385,f438])).

fof(f385,plain,
    ( ! [X2] :
        ( k10_yellow_6(sK0,sK3(sK0)) = k10_yellow_6(sK0,sK2(sK3(sK0)))
        | ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k10_yellow_6(sK0,sK3(sK0))),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(resolution,[],[f349,f326])).

fof(f326,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),X1)
        | ~ r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),X1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_22 ),
    inference(resolution,[],[f314,f72])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK2(sK3(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_22 ),
    inference(resolution,[],[f253,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f253,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0)))) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f252])).

fof(f1166,plain,
    ( ~ spl7_67
    | spl7_51 ),
    inference(avatar_split_clause,[],[f1051,f1038,f1163])).

fof(f1038,plain,
    ( spl7_51
  <=> r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f1051,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),k1_zfmisc_1(sK4(sK0,sK1)))
    | spl7_51 ),
    inference(resolution,[],[f1040,f75])).

fof(f1040,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | spl7_51 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1041,plain,
    ( ~ spl7_51
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f1028,f157,f148,f138,f133,f118,f114,f91,f86,f81,f1038])).

fof(f1028,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f1027,f150])).

fof(f1027,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f1026,f140])).

fof(f1026,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f1025,f135])).

fof(f1025,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f1024,f120])).

fof(f1024,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(duplicate_literal_removal,[],[f1021])).

fof(f1021,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(resolution,[],[f893,f158])).

fof(f893,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,sK4(sK0,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X0))),sK4(sK0,X0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(resolution,[],[f798,f74])).

fof(f798,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2)))
        | ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f797,f115])).

fof(f797,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2)))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f796,f83])).

fof(f796,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2)))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | v2_struct_0(sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f795,f93])).

fof(f795,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | v2_struct_0(sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f794,f88])).

fof(f794,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,sK4(sK0,X2))
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | v2_struct_0(sK0)
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(resolution,[],[f711,f51])).

fof(f711,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X2)
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f710,f135])).

fof(f710,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X2)
        | ~ v4_orders_2(sK1)
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f709,f120])).

fof(f709,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X2)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f705,f140])).

fof(f705,plain,
    ( ! [X2] :
        ( ~ v7_waybel_0(sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X2)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f150,f215])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(k10_yellow_6(sK0,sK5(sK0,X0,X1)),k1_zfmisc_1(X1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f189,f75])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k10_yellow_6(sK0,sK5(sK0,X0,X1)),X1)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f106,f76])).

fof(f106,plain,
    ( ! [X6,X5] :
        ( r2_hidden(X6,k10_yellow_6(sK0,sK5(sK0,X5,X6)))
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X5,X6)
        | v2_struct_0(X5) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f105,f93])).

fof(f105,plain,
    ( ! [X6,X5] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X5,X6)
        | r2_hidden(X6,k10_yellow_6(sK0,sK5(sK0,X5,X6))) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f97,f83])).

fof(f97,plain,
    ( ! [X6,X5] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X5,X6)
        | r2_hidden(X6,k10_yellow_6(sK0,sK5(sK0,X5,X6))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f718,plain,
    ( spl7_4
    | spl7_44 ),
    inference(avatar_split_clause,[],[f39,f716,f114])).

fof(f39,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | v3_yellow_6(sK2(X1),sK0)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f491,plain,
    ( spl7_36
    | spl7_37
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f426,f168,f488,f485])).

fof(f168,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f426,plain,
    ( ! [X2] :
        ( r2_hidden(k1_xboole_0,k1_xboole_0)
        | r1_tarski(k1_xboole_0,X2) )
    | ~ spl7_13 ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,
    ( ! [X2] :
        ( r2_hidden(k1_xboole_0,k1_xboole_0)
        | r1_tarski(k1_xboole_0,X2)
        | r1_tarski(k1_xboole_0,X2) )
    | ~ spl7_13 ),
    inference(superposition,[],[f72,f393])).

fof(f393,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK6(k1_xboole_0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f389,f72])).

fof(f389,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | k1_xboole_0 = X5 )
    | ~ spl7_13 ),
    inference(resolution,[],[f356,f48])).

fof(f356,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X1,X2) )
    | ~ spl7_13 ),
    inference(resolution,[],[f341,f77])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl7_13 ),
    inference(resolution,[],[f336,f75])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f335,f70])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f332,f48])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f279,f72])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(k1_xboole_0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl7_13 ),
    inference(resolution,[],[f261,f70])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ r2_hidden(sK6(k1_xboole_0,X1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_13 ),
    inference(resolution,[],[f234,f72])).

fof(f234,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X7,X8) )
    | ~ spl7_13 ),
    inference(resolution,[],[f218,f48])).

fof(f218,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k10_yellow_6(sK0,sK3(sK0))))
        | ~ r2_hidden(X4,X6)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X4,X5) )
    | ~ spl7_13 ),
    inference(resolution,[],[f207,f75])).

fof(f207,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X4,k10_yellow_6(sK0,sK3(sK0)))
        | ~ r2_hidden(X3,X2)
        | ~ r2_hidden(X3,X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_13 ),
    inference(resolution,[],[f204,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_13 ),
    inference(resolution,[],[f169,f77])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f378,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | spl7_12
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | spl7_27 ),
    inference(avatar_split_clause,[],[f364,f351,f143,f91,f86,f81,f164,f175,f171])).

fof(f351,plain,
    ( spl7_27
  <=> m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f364,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f363,f83])).

fof(f363,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f362,f145])).

fof(f362,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_27 ),
    inference(subsumption_resolution,[],[f361,f93])).

fof(f361,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | spl7_27 ),
    inference(subsumption_resolution,[],[f358,f88])).

fof(f358,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | spl7_27 ),
    inference(resolution,[],[f353,f67])).

fof(f353,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f351])).

fof(f354,plain,
    ( spl7_26
    | ~ spl7_27
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f331,f168,f351,f348])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0)))
        | k10_yellow_6(sK0,sK3(sK0)) = X0 )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f328,f70])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0)))
        | k10_yellow_6(sK0,sK3(sK0)) = X0
        | r1_tarski(k10_yellow_6(sK0,sK3(sK0)),X0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f230,f72])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(k10_yellow_6(sK0,sK3(sK0)),X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0)))
        | k10_yellow_6(sK0,sK3(sK0)) = X0 )
    | ~ spl7_13 ),
    inference(resolution,[],[f206,f70])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_yellow_6(sK0,sK3(sK0)),X1)
        | ~ r2_hidden(sK6(k10_yellow_6(sK0,sK3(sK0)),X1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_13 ),
    inference(resolution,[],[f204,f72])).

fof(f312,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | spl7_12
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f311,f264,f236,f143,f114,f81,f164,f175,f171])).

fof(f311,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f310,f83])).

fof(f310,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f309,f265])).

fof(f309,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f308,f145])).

fof(f308,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK3(sK0))
    | spl7_4
    | ~ spl7_18 ),
    inference(resolution,[],[f306,f122])).

fof(f122,plain,
    ( ! [X1] :
        ( m2_yellow_6(sK2(X1),sK0,X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | v2_struct_0(X1) )
    | spl7_4 ),
    inference(subsumption_resolution,[],[f38,f116])).

fof(f116,plain,
    ( ~ v1_compts_1(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f38,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | m2_yellow_6(sK2(X1),sK0,X1)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK2(sK3(sK0)),X0,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f238,f63])).

fof(f238,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f236])).

fof(f304,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | spl7_12
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | spl7_21
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f303,f264,f248,f143,f114,f81,f164,f175,f171])).

fof(f303,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | spl7_21
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f302,f83])).

fof(f302,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_8
    | spl7_21
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f301,f265])).

fof(f301,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_8
    | spl7_21 ),
    inference(subsumption_resolution,[],[f300,f145])).

fof(f300,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_4
    | spl7_21 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK3(sK0))
    | spl7_4
    | spl7_21 ),
    inference(resolution,[],[f295,f122])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK2(sK3(sK0)),X0,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | spl7_21 ),
    inference(resolution,[],[f250,f64])).

fof(f250,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f248])).

fof(f293,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | spl7_12
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | spl7_20
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f292,f264,f244,f143,f114,f81,f164,f175,f171])).

fof(f292,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | spl7_20
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f291,f83])).

fof(f291,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_8
    | spl7_20
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f290,f265])).

fof(f290,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_4
    | ~ spl7_8
    | spl7_20 ),
    inference(subsumption_resolution,[],[f289,f145])).

fof(f289,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_4
    | spl7_20 ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK3(sK0))
    | spl7_4
    | spl7_20 ),
    inference(resolution,[],[f285,f122])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK2(sK3(sK0)),X0,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | spl7_20 ),
    inference(resolution,[],[f246,f65])).

fof(f246,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f284,plain,
    ( spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | spl7_19
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f283,f264,f240,f143,f114,f81,f175,f171,f164])).

fof(f283,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | spl7_1
    | spl7_4
    | ~ spl7_8
    | spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f282,f145])).

fof(f282,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK3(sK0))
    | spl7_1
    | spl7_4
    | spl7_19
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK3(sK0))
    | spl7_1
    | spl7_4
    | spl7_19
    | ~ spl7_24 ),
    inference(resolution,[],[f274,f122])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK2(sK3(sK0)),sK0,X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0) )
    | spl7_1
    | spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f256,f265])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m2_yellow_6(sK2(sK3(sK0)),sK0,X0) )
    | spl7_1
    | spl7_19 ),
    inference(subsumption_resolution,[],[f255,f83])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m2_yellow_6(sK2(sK3(sK0)),sK0,X0)
        | v2_struct_0(sK0) )
    | spl7_19 ),
    inference(resolution,[],[f242,f66])).

fof(f242,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f273,plain,
    ( ~ spl7_3
    | spl7_24 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl7_3
    | spl7_24 ),
    inference(subsumption_resolution,[],[f271,f93])).

fof(f271,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_24 ),
    inference(resolution,[],[f266,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f266,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f264])).

fof(f254,plain,
    ( spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | spl7_22
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f225,f220,f91,f86,f81,f252,f248,f244,f240,f236])).

fof(f220,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f225,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v4_orders_2(sK2(sK3(sK0)))
        | ~ v7_waybel_0(sK2(sK3(sK0)))
        | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
        | ~ r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0))))
        | v2_struct_0(sK2(sK3(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v4_orders_2(sK2(sK3(sK0)))
        | ~ v7_waybel_0(sK2(sK3(sK0)))
        | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0))))
        | v2_struct_0(sK2(sK3(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(resolution,[],[f221,f108])).

fof(f108,plain,
    ( ! [X8,X7] :
        ( r3_waybel_9(sK0,X7,X8)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,k10_yellow_6(sK0,X7))
        | v2_struct_0(X7) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f107,f93])).

fof(f107,plain,
    ( ! [X8,X7] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,k10_yellow_6(sK0,X7))
        | r3_waybel_9(sK0,X7,X8) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f98,f83])).

fof(f98,plain,
    ( ! [X8,X7] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,k10_yellow_6(sK0,X7))
        | r3_waybel_9(sK0,X7,X8) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f221,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | spl7_17
    | spl7_4
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f214,f209,f143,f114,f220,f175,f171,f164])).

fof(f209,plain,
    ( spl7_16
  <=> ! [X1,X0] :
        ( ~ m2_yellow_6(X0,sK0,sK3(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | v2_struct_0(sK3(sK0)) )
    | spl7_4
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f212,f145])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | v2_struct_0(sK3(sK0)) )
    | spl7_4
    | ~ spl7_16 ),
    inference(resolution,[],[f210,f122])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(X0,sK0,sK3(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl7_12
    | spl7_16
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f188,f143,f114,f91,f86,f81,f175,f171,f209,f164])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ m2_yellow_6(X0,sK0,sK3(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(sK3(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f180,f145])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | ~ m2_yellow_6(X0,sK0,sK3(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(sK3(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | ~ m2_yellow_6(X0,sK0,sK3(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(sK3(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(resolution,[],[f102,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK3(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f127,f83])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK3(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f126,f93])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK3(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f124,f88])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK3(sK0),X0)
        | v2_struct_0(sK0) )
    | spl7_4 ),
    inference(resolution,[],[f116,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( r3_waybel_9(sK0,X0,X2)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m2_yellow_6(X1,sK0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X1,X2)
        | v2_struct_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f101,f93])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m2_yellow_6(X1,sK0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X1,X2)
        | r3_waybel_9(sK0,X0,X2) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f95,f83])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m2_yellow_6(X1,sK0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X1,X2)
        | r3_waybel_9(sK0,X0,X2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X3)
      | r3_waybel_9(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f203,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f201,f116])).

fof(f201,plain,
    ( v1_compts_1(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f200,f83])).

fof(f200,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f199,f93])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f197,f88])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f166,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f166,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f196,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | spl7_15 ),
    inference(subsumption_resolution,[],[f194,f116])).

fof(f194,plain,
    ( v1_compts_1(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_15 ),
    inference(subsumption_resolution,[],[f193,f83])).

fof(f193,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_15 ),
    inference(subsumption_resolution,[],[f192,f93])).

fof(f192,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | spl7_15 ),
    inference(subsumption_resolution,[],[f190,f88])).

fof(f190,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | spl7_15 ),
    inference(resolution,[],[f177,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v4_orders_2(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f177,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f187,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | spl7_14 ),
    inference(subsumption_resolution,[],[f185,f116])).

fof(f185,plain,
    ( v1_compts_1(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_14 ),
    inference(subsumption_resolution,[],[f184,f83])).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_14 ),
    inference(subsumption_resolution,[],[f183,f93])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | spl7_14 ),
    inference(subsumption_resolution,[],[f181,f88])).

fof(f181,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | spl7_14 ),
    inference(resolution,[],[f173,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v7_waybel_0(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f173,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f178,plain,
    ( spl7_12
    | spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f162,f143,f114,f91,f86,f81,f175,f171,f168,f164])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0)))
        | v2_struct_0(sK3(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f161,f145])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0)))
        | v2_struct_0(sK3(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0)))
        | v2_struct_0(sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(resolution,[],[f108,f128])).

fof(f159,plain,
    ( ~ spl7_4
    | spl7_11
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f112,f91,f86,f81,f157,f114])).

fof(f112,plain,
    ( ! [X10] :
        ( v2_struct_0(X10)
        | ~ v4_orders_2(X10)
        | ~ v7_waybel_0(X10)
        | ~ l1_waybel_0(X10,sK0)
        | r3_waybel_9(sK0,X10,sK4(sK0,X10))
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f111,f93])).

fof(f111,plain,
    ( ! [X10] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X10)
        | ~ v4_orders_2(X10)
        | ~ v7_waybel_0(X10)
        | ~ l1_waybel_0(X10,sK0)
        | r3_waybel_9(sK0,X10,sK4(sK0,X10))
        | ~ v1_compts_1(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f100,f83])).

fof(f100,plain,
    ( ! [X10] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X10)
        | ~ v4_orders_2(X10)
        | ~ v7_waybel_0(X10)
        | ~ l1_waybel_0(X10,sK0)
        | r3_waybel_9(sK0,X10,sK4(sK0,X10))
        | ~ v1_compts_1(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f155,plain,
    ( ~ spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f40,f153,f114])).

fof(f40,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f151,plain,
    ( ~ spl7_4
    | spl7_9 ),
    inference(avatar_split_clause,[],[f44,f148,f114])).

fof(f44,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f146,plain,
    ( spl7_8
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f131,f114,f91,f86,f81,f143])).

fof(f131,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f130,f83])).

fof(f130,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f129,f93])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f125,f88])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | spl7_4 ),
    inference(resolution,[],[f116,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | l1_waybel_0(sK3(X0),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,
    ( ~ spl7_4
    | spl7_7 ),
    inference(avatar_split_clause,[],[f43,f138,f114])).

fof(f43,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f136,plain,
    ( ~ spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f42,f133,f114])).

fof(f42,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f121,plain,
    ( ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f41,f118,f114])).

fof(f41,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f47,f91])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (3872)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (3880)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (3874)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (3882)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (3882)Refutation not found, incomplete strategy% (3882)------------------------------
% 0.21/0.53  % (3882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3882)Memory used [KB]: 10874
% 0.21/0.53  % (3882)Time elapsed: 0.015 s
% 0.21/0.53  % (3882)------------------------------
% 0.21/0.53  % (3882)------------------------------
% 0.21/0.53  % (3888)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (3864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (3865)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3866)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (3867)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3879)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (3887)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (3862)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (3875)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (3871)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (3861)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (3860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (3877)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (3889)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (3884)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (3870)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (3876)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (3869)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (3863)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (3883)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (3868)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (3885)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (3881)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (3886)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (3878)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (3873)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.82/0.61  % (3921)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.38/0.83  % (3865)Time limit reached!
% 3.38/0.83  % (3865)------------------------------
% 3.38/0.83  % (3865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.38/0.83  % (3865)Termination reason: Time limit
% 3.38/0.83  
% 3.38/0.83  % (3865)Memory used [KB]: 7675
% 3.38/0.83  % (3865)Time elapsed: 0.407 s
% 3.38/0.83  % (3865)------------------------------
% 3.38/0.83  % (3865)------------------------------
% 3.38/0.85  % (3880)Refutation found. Thanks to Tanya!
% 3.38/0.85  % SZS status Theorem for theBenchmark
% 3.38/0.85  % SZS output start Proof for theBenchmark
% 3.38/0.85  fof(f2388,plain,(
% 3.38/0.85    $false),
% 3.38/0.85    inference(avatar_sat_refutation,[],[f84,f89,f94,f121,f136,f141,f146,f151,f155,f159,f178,f187,f196,f203,f211,f222,f254,f273,f284,f293,f304,f312,f354,f378,f491,f718,f1041,f1166,f1239,f1455,f1527,f1540,f1726,f2106,f2125,f2366,f2387])).
% 3.38/0.85  fof(f2387,plain,(
% 3.38/0.85    ~spl7_8 | spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_44 | spl7_128),
% 3.38/0.85    inference(avatar_contradiction_clause,[],[f2386])).
% 3.38/0.85  fof(f2386,plain,(
% 3.38/0.85    $false | (~spl7_8 | spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_44 | spl7_128)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2385,f176])).
% 3.38/0.85  fof(f176,plain,(
% 3.38/0.85    v4_orders_2(sK3(sK0)) | ~spl7_15),
% 3.38/0.85    inference(avatar_component_clause,[],[f175])).
% 3.38/0.85  fof(f175,plain,(
% 3.38/0.85    spl7_15 <=> v4_orders_2(sK3(sK0))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 3.38/0.85  fof(f2385,plain,(
% 3.38/0.85    ~v4_orders_2(sK3(sK0)) | (~spl7_8 | spl7_12 | ~spl7_14 | ~spl7_44 | spl7_128)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2384,f172])).
% 3.38/0.85  fof(f172,plain,(
% 3.38/0.85    v7_waybel_0(sK3(sK0)) | ~spl7_14),
% 3.38/0.85    inference(avatar_component_clause,[],[f171])).
% 3.38/0.85  fof(f171,plain,(
% 3.38/0.85    spl7_14 <=> v7_waybel_0(sK3(sK0))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 3.38/0.85  fof(f2384,plain,(
% 3.38/0.85    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | (~spl7_8 | spl7_12 | ~spl7_44 | spl7_128)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2383,f145])).
% 3.38/0.85  fof(f145,plain,(
% 3.38/0.85    l1_waybel_0(sK3(sK0),sK0) | ~spl7_8),
% 3.38/0.85    inference(avatar_component_clause,[],[f143])).
% 3.38/0.85  fof(f143,plain,(
% 3.38/0.85    spl7_8 <=> l1_waybel_0(sK3(sK0),sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 3.38/0.85  fof(f2383,plain,(
% 3.38/0.85    ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | (spl7_12 | ~spl7_44 | spl7_128)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2381,f165])).
% 3.38/0.85  fof(f165,plain,(
% 3.38/0.85    ~v2_struct_0(sK3(sK0)) | spl7_12),
% 3.38/0.85    inference(avatar_component_clause,[],[f164])).
% 3.38/0.85  fof(f164,plain,(
% 3.38/0.85    spl7_12 <=> v2_struct_0(sK3(sK0))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 3.38/0.85  fof(f2381,plain,(
% 3.38/0.85    v2_struct_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | (~spl7_44 | spl7_128)),
% 3.38/0.85    inference(resolution,[],[f2365,f717])).
% 3.38/0.85  fof(f717,plain,(
% 3.38/0.85    ( ! [X1] : (v3_yellow_6(sK2(X1),sK0) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1)) ) | ~spl7_44),
% 3.38/0.85    inference(avatar_component_clause,[],[f716])).
% 3.38/0.85  fof(f716,plain,(
% 3.38/0.85    spl7_44 <=> ! [X1] : (v2_struct_0(X1) | v3_yellow_6(sK2(X1),sK0) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 3.38/0.85  fof(f2365,plain,(
% 3.38/0.85    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | spl7_128),
% 3.38/0.85    inference(avatar_component_clause,[],[f2363])).
% 3.38/0.85  fof(f2363,plain,(
% 3.38/0.85    spl7_128 <=> v3_yellow_6(sK2(sK3(sK0)),sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).
% 3.38/0.85  fof(f2366,plain,(
% 3.38/0.85    ~spl7_128 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_74),
% 3.38/0.85    inference(avatar_split_clause,[],[f2359,f1236,f248,f244,f240,f236,f91,f86,f81,f2363])).
% 3.38/0.85  fof(f81,plain,(
% 3.38/0.85    spl7_1 <=> v2_struct_0(sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 3.38/0.85  fof(f86,plain,(
% 3.38/0.85    spl7_2 <=> v2_pre_topc(sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 3.38/0.85  fof(f91,plain,(
% 3.38/0.85    spl7_3 <=> l1_pre_topc(sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 3.38/0.85  fof(f236,plain,(
% 3.38/0.85    spl7_18 <=> v2_struct_0(sK2(sK3(sK0)))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 3.38/0.85  fof(f240,plain,(
% 3.38/0.85    spl7_19 <=> l1_waybel_0(sK2(sK3(sK0)),sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 3.38/0.85  fof(f244,plain,(
% 3.38/0.85    spl7_20 <=> v7_waybel_0(sK2(sK3(sK0)))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 3.38/0.85  fof(f248,plain,(
% 3.38/0.85    spl7_21 <=> v4_orders_2(sK2(sK3(sK0)))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 3.38/0.85  fof(f1236,plain,(
% 3.38/0.85    spl7_74 <=> k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 3.38/0.85  fof(f2359,plain,(
% 3.38/0.85    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2358,f83])).
% 3.38/0.85  fof(f83,plain,(
% 3.38/0.85    ~v2_struct_0(sK0) | spl7_1),
% 3.38/0.85    inference(avatar_component_clause,[],[f81])).
% 3.38/0.85  fof(f2358,plain,(
% 3.38/0.85    v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2357,f241])).
% 3.38/0.85  fof(f241,plain,(
% 3.38/0.85    l1_waybel_0(sK2(sK3(sK0)),sK0) | ~spl7_19),
% 3.38/0.85    inference(avatar_component_clause,[],[f240])).
% 3.38/0.85  fof(f2357,plain,(
% 3.38/0.85    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_20 | ~spl7_21 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2356,f245])).
% 3.38/0.85  fof(f245,plain,(
% 3.38/0.85    v7_waybel_0(sK2(sK3(sK0))) | ~spl7_20),
% 3.38/0.85    inference(avatar_component_clause,[],[f244])).
% 3.38/0.85  fof(f2356,plain,(
% 3.38/0.85    ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_21 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2355,f249])).
% 3.38/0.85  fof(f249,plain,(
% 3.38/0.85    v4_orders_2(sK2(sK3(sK0))) | ~spl7_21),
% 3.38/0.85    inference(avatar_component_clause,[],[f248])).
% 3.38/0.85  fof(f2355,plain,(
% 3.38/0.85    ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2354,f237])).
% 3.38/0.85  fof(f237,plain,(
% 3.38/0.85    ~v2_struct_0(sK2(sK3(sK0))) | spl7_18),
% 3.38/0.85    inference(avatar_component_clause,[],[f236])).
% 3.38/0.85  fof(f2354,plain,(
% 3.38/0.85    v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2353,f93])).
% 3.38/0.85  fof(f93,plain,(
% 3.38/0.85    l1_pre_topc(sK0) | ~spl7_3),
% 3.38/0.85    inference(avatar_component_clause,[],[f91])).
% 3.38/0.85  fof(f2353,plain,(
% 3.38/0.85    ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | (~spl7_2 | ~spl7_74)),
% 3.38/0.85    inference(subsumption_resolution,[],[f2352,f88])).
% 3.38/0.85  fof(f88,plain,(
% 3.38/0.85    v2_pre_topc(sK0) | ~spl7_2),
% 3.38/0.85    inference(avatar_component_clause,[],[f86])).
% 3.38/0.85  fof(f2352,plain,(
% 3.38/0.85    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~spl7_74),
% 3.38/0.85    inference(trivial_inequality_removal,[],[f2351])).
% 3.38/0.85  fof(f2351,plain,(
% 3.38/0.85    k1_xboole_0 != k1_xboole_0 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~spl7_74),
% 3.38/0.85    inference(superposition,[],[f58,f1238])).
% 3.38/0.85  fof(f1238,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) | ~spl7_74),
% 3.38/0.85    inference(avatar_component_clause,[],[f1236])).
% 3.38/0.85  fof(f58,plain,(
% 3.38/0.85    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | ~v3_yellow_6(X1,X0)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f23])).
% 3.38/0.85  fof(f23,plain,(
% 3.38/0.85    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.38/0.85    inference(flattening,[],[f22])).
% 3.38/0.85  fof(f22,plain,(
% 3.38/0.85    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.38/0.85    inference(ennf_transformation,[],[f10])).
% 3.38/0.85  fof(f10,axiom,(
% 3.38/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 3.38/0.85  fof(f2125,plain,(
% 3.38/0.85    ~spl7_37),
% 3.38/0.85    inference(avatar_contradiction_clause,[],[f2124])).
% 3.38/0.85  fof(f2124,plain,(
% 3.38/0.85    $false | ~spl7_37),
% 3.38/0.85    inference(subsumption_resolution,[],[f2117,f79])).
% 3.38/0.85  fof(f79,plain,(
% 3.38/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.38/0.85    inference(equality_resolution,[],[f68])).
% 3.38/0.85  fof(f68,plain,(
% 3.38/0.85    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.38/0.85    inference(cnf_transformation,[],[f2])).
% 3.38/0.85  fof(f2,axiom,(
% 3.38/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.38/0.85  fof(f2117,plain,(
% 3.38/0.85    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl7_37),
% 3.38/0.85    inference(resolution,[],[f490,f76])).
% 3.38/0.85  fof(f76,plain,(
% 3.38/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f35])).
% 3.38/0.85  fof(f35,plain,(
% 3.38/0.85    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.38/0.85    inference(ennf_transformation,[],[f6])).
% 3.38/0.85  fof(f6,axiom,(
% 3.38/0.85    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.38/0.85  fof(f490,plain,(
% 3.38/0.85    r2_hidden(k1_xboole_0,k1_xboole_0) | ~spl7_37),
% 3.38/0.85    inference(avatar_component_clause,[],[f488])).
% 3.38/0.85  fof(f488,plain,(
% 3.38/0.85    spl7_37 <=> r2_hidden(k1_xboole_0,k1_xboole_0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 3.38/0.85  fof(f2106,plain,(
% 3.38/0.85    spl7_74 | ~spl7_36 | ~spl7_84),
% 3.38/0.85    inference(avatar_split_clause,[],[f2028,f1448,f485,f1236])).
% 3.38/0.85  fof(f485,plain,(
% 3.38/0.85    spl7_36 <=> ! [X2] : r1_tarski(k1_xboole_0,X2)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 3.38/0.85  fof(f1448,plain,(
% 3.38/0.85    spl7_84 <=> r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 3.38/0.85  fof(f2028,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) | (~spl7_36 | ~spl7_84)),
% 3.38/0.85    inference(resolution,[],[f1450,f497])).
% 3.38/0.85  fof(f497,plain,(
% 3.38/0.85    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl7_36),
% 3.38/0.85    inference(resolution,[],[f486,f70])).
% 3.38/0.85  fof(f70,plain,(
% 3.38/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.38/0.85    inference(cnf_transformation,[],[f2])).
% 3.38/0.85  fof(f486,plain,(
% 3.38/0.85    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl7_36),
% 3.38/0.85    inference(avatar_component_clause,[],[f485])).
% 3.38/0.85  fof(f1450,plain,(
% 3.38/0.85    r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0) | ~spl7_84),
% 3.38/0.85    inference(avatar_component_clause,[],[f1448])).
% 3.38/0.85  fof(f1726,plain,(
% 3.38/0.85    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24 | spl7_67),
% 3.38/0.85    inference(avatar_contradiction_clause,[],[f1725])).
% 3.38/0.85  fof(f1725,plain,(
% 3.38/0.85    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24 | spl7_67)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1713,f48])).
% 3.38/0.85  fof(f48,plain,(
% 3.38/0.85    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.38/0.85    inference(cnf_transformation,[],[f3])).
% 3.38/0.85  fof(f3,axiom,(
% 3.38/0.85    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.38/0.85  fof(f1713,plain,(
% 3.38/0.85    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(sK0,sK1))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24 | spl7_67)),
% 3.38/0.85    inference(backward_demodulation,[],[f1165,f1707])).
% 3.38/0.85  fof(f1707,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1706,f150])).
% 3.38/0.85  fof(f150,plain,(
% 3.38/0.85    l1_waybel_0(sK1,sK0) | ~spl7_9),
% 3.38/0.85    inference(avatar_component_clause,[],[f148])).
% 3.38/0.85  fof(f148,plain,(
% 3.38/0.85    spl7_9 <=> l1_waybel_0(sK1,sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 3.38/0.85  fof(f1706,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_waybel_0(sK1,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1705,f140])).
% 3.38/0.85  fof(f140,plain,(
% 3.38/0.85    v7_waybel_0(sK1) | ~spl7_7),
% 3.38/0.85    inference(avatar_component_clause,[],[f138])).
% 3.38/0.85  fof(f138,plain,(
% 3.38/0.85    spl7_7 <=> v7_waybel_0(sK1)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 3.38/0.85  fof(f1705,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1704,f135])).
% 3.38/0.85  fof(f135,plain,(
% 3.38/0.85    v4_orders_2(sK1) | ~spl7_6),
% 3.38/0.85    inference(avatar_component_clause,[],[f133])).
% 3.38/0.85  fof(f133,plain,(
% 3.38/0.85    spl7_6 <=> v4_orders_2(sK1)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 3.38/0.85  fof(f1704,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1703,f120])).
% 3.38/0.85  fof(f120,plain,(
% 3.38/0.85    ~v2_struct_0(sK1) | spl7_5),
% 3.38/0.85    inference(avatar_component_clause,[],[f118])).
% 3.38/0.85  fof(f118,plain,(
% 3.38/0.85    spl7_5 <=> v2_struct_0(sK1)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 3.38/0.85  fof(f1703,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24)),
% 3.38/0.85    inference(duplicate_literal_removal,[],[f1700])).
% 3.38/0.85  fof(f1700,plain,(
% 3.38/0.85    k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_24)),
% 3.38/0.85    inference(resolution,[],[f1188,f158])).
% 3.38/0.85  fof(f158,plain,(
% 3.38/0.85    ( ! [X10] : (r3_waybel_9(sK0,X10,sK4(sK0,X10)) | v2_struct_0(X10) | ~l1_waybel_0(X10,sK0) | ~v7_waybel_0(X10) | ~v4_orders_2(X10)) ) | ~spl7_11),
% 3.38/0.85    inference(avatar_component_clause,[],[f157])).
% 3.38/0.85  fof(f157,plain,(
% 3.38/0.85    spl7_11 <=> ! [X10] : (v2_struct_0(X10) | r3_waybel_9(sK0,X10,sK4(sK0,X10)) | ~l1_waybel_0(X10,sK0) | ~v7_waybel_0(X10) | ~v4_orders_2(X10))),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 3.38/0.85  fof(f1188,plain,(
% 3.38/0.85    ( ! [X2] : (~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1187,f115])).
% 3.38/0.85  fof(f115,plain,(
% 3.38/0.85    v1_compts_1(sK0) | ~spl7_4),
% 3.38/0.85    inference(avatar_component_clause,[],[f114])).
% 3.38/0.85  fof(f114,plain,(
% 3.38/0.85    spl7_4 <=> v1_compts_1(sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 3.38/0.85  fof(f1187,plain,(
% 3.38/0.85    ( ! [X2] : (k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))) | ~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1186,f83])).
% 3.38/0.85  fof(f1186,plain,(
% 3.38/0.85    ( ! [X2] : (k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))) | ~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1185,f93])).
% 3.38/0.85  fof(f1185,plain,(
% 3.38/0.85    ( ! [X2] : (k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))) | ~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1184,f88])).
% 3.38/0.85  fof(f1184,plain,(
% 3.38/0.85    ( ! [X2] : (k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))) | ~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(resolution,[],[f1105,f51])).
% 3.38/0.85  fof(f51,plain,(
% 3.38/0.85    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | ~v1_compts_1(X0)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f21])).
% 3.38/0.85  fof(f21,plain,(
% 3.38/0.85    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.38/0.85    inference(flattening,[],[f20])).
% 3.38/0.85  fof(f20,plain,(
% 3.38/0.85    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.38/0.85    inference(ennf_transformation,[],[f14])).
% 3.38/0.85  fof(f14,axiom,(
% 3.38/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).
% 3.38/0.85  fof(f1105,plain,(
% 3.38/0.85    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~r3_waybel_9(sK0,sK1,X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1104,f83])).
% 3.38/0.85  fof(f1104,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1103,f150])).
% 3.38/0.85  fof(f1103,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1102,f140])).
% 3.38/0.85  fof(f1102,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1101,f135])).
% 3.38/0.85  fof(f1101,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1100,f120])).
% 3.38/0.85  fof(f1100,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f1099,f265])).
% 3.38/0.85  fof(f265,plain,(
% 3.38/0.85    l1_struct_0(sK0) | ~spl7_24),
% 3.38/0.85    inference(avatar_component_clause,[],[f264])).
% 3.38/0.85  fof(f264,plain,(
% 3.38/0.85    spl7_24 <=> l1_struct_0(sK0)),
% 3.38/0.85    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 3.38/0.85  fof(f1099,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(duplicate_literal_removal,[],[f1098])).
% 3.38/0.85  fof(f1098,plain,(
% 3.38/0.85    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(resolution,[],[f951,f104])).
% 3.38/0.85  fof(f104,plain,(
% 3.38/0.85    ( ! [X4,X3] : (m2_yellow_6(sK5(sK0,X3,X4),sK0,X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X3,X4) | v2_struct_0(X3)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 3.38/0.85    inference(subsumption_resolution,[],[f103,f93])).
% 3.38/0.85  fof(f103,plain,(
% 3.38/0.85    ( ! [X4,X3] : (~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X3,X4) | m2_yellow_6(sK5(sK0,X3,X4),sK0,X3)) ) | (spl7_1 | ~spl7_2)),
% 3.38/0.85    inference(subsumption_resolution,[],[f96,f83])).
% 3.38/0.85  fof(f96,plain,(
% 3.38/0.85    ( ! [X4,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X3,X4) | m2_yellow_6(sK5(sK0,X3,X4),sK0,X3)) ) | ~spl7_2),
% 3.38/0.85    inference(resolution,[],[f88,f60])).
% 3.38/0.85  fof(f60,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m2_yellow_6(sK5(X0,X1,X2),X0,X1)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f27])).
% 3.38/0.85  fof(f27,plain,(
% 3.38/0.85    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.38/0.85    inference(flattening,[],[f26])).
% 3.38/0.85  fof(f26,plain,(
% 3.38/0.85    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.38/0.85    inference(ennf_transformation,[],[f13])).
% 3.38/0.85  fof(f13,axiom,(
% 3.38/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 3.38/0.85  fof(f951,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~m2_yellow_6(sK5(sK0,sK1,X0),X1,X2) | ~r3_waybel_9(sK0,sK1,X0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f950,f150])).
% 3.38/0.85  fof(f950,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~l1_waybel_0(sK1,sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,X1) | ~m2_yellow_6(sK5(sK0,sK1,X0),X1,X2) | v2_struct_0(X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f949,f140])).
% 3.38/0.85  fof(f949,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,X1) | ~m2_yellow_6(sK5(sK0,sK1,X0),X1,X2) | v2_struct_0(X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f948,f135])).
% 3.38/0.85  fof(f948,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,X1) | ~m2_yellow_6(sK5(sK0,sK1,X0),X1,X2) | v2_struct_0(X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f947,f120])).
% 3.38/0.85  fof(f947,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,X1) | ~m2_yellow_6(sK5(sK0,sK1,X0),X1,X2) | v2_struct_0(X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(duplicate_literal_removal,[],[f946])).
% 3.38/0.85  fof(f946,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,X1) | ~m2_yellow_6(sK5(sK0,sK1,X0),X1,X2) | v2_struct_0(X1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(resolution,[],[f836,f104])).
% 3.38/0.85  fof(f836,plain,(
% 3.38/0.85    ( ! [X2,X0,X3,X1] : (~m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | ~l1_struct_0(X2) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,X2) | ~m2_yellow_6(sK5(sK0,sK1,X0),X2,X3) | v2_struct_0(X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f835,f63])).
% 3.38/0.85  fof(f63,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v2_struct_0(X0)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f31])).
% 3.38/0.85  fof(f31,plain,(
% 3.38/0.85    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.38/0.85    inference(flattening,[],[f30])).
% 3.38/0.85  fof(f30,plain,(
% 3.38/0.85    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.38/0.85    inference(ennf_transformation,[],[f9])).
% 3.38/0.85  fof(f9,axiom,(
% 3.38/0.85    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.38/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 3.38/0.85  fof(f835,plain,(
% 3.38/0.85    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | ~m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1) | ~l1_struct_0(X2) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,X2) | ~m2_yellow_6(sK5(sK0,sK1,X0),X2,X3) | v2_struct_0(X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f834,f64])).
% 3.38/0.85  fof(f64,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v2_struct_0(X0)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f31])).
% 3.38/0.85  fof(f834,plain,(
% 3.38/0.85    ( ! [X2,X0,X3,X1] : (~v4_orders_2(sK5(sK0,sK1,X0)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | ~m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1) | ~l1_struct_0(X2) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,X2) | ~m2_yellow_6(sK5(sK0,sK1,X0),X2,X3) | v2_struct_0(X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(resolution,[],[f784,f65])).
% 3.38/0.85  fof(f65,plain,(
% 3.38/0.85    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v2_struct_0(X0)) )),
% 3.38/0.85    inference(cnf_transformation,[],[f31])).
% 3.38/0.85  fof(f784,plain,(
% 3.38/0.85    ( ! [X0,X1] : (~v7_waybel_0(sK5(sK0,sK1,X0)) | ~v4_orders_2(sK5(sK0,sK1,X0)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | ~m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f783,f83])).
% 3.38/0.85  fof(f783,plain,(
% 3.38/0.85    ( ! [X0,X1] : (~v7_waybel_0(sK5(sK0,sK1,X0)) | ~v4_orders_2(sK5(sK0,sK1,X0)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | ~m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_24)),
% 3.38/0.85    inference(subsumption_resolution,[],[f782,f265])).
% 3.38/0.85  fof(f782,plain,(
% 3.38/0.85    ( ! [X0,X1] : (~v7_waybel_0(sK5(sK0,sK1,X0)) | ~v4_orders_2(sK5(sK0,sK1,X0)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~l1_struct_0(sK0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | ~m2_yellow_6(sK5(sK0,sK1,X0),sK0,X1) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10)),
% 3.38/0.85    inference(resolution,[],[f746,f66])).
% 3.38/0.87  fof(f66,plain,(
% 3.38/0.87    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v2_struct_0(X0)) )),
% 3.38/0.87    inference(cnf_transformation,[],[f31])).
% 3.38/0.87  fof(f746,plain,(
% 3.38/0.87    ( ! [X0] : (~l1_waybel_0(sK5(sK0,sK1,X0),sK0) | ~v7_waybel_0(sK5(sK0,sK1,X0)) | ~v4_orders_2(sK5(sK0,sK1,X0)) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10)),
% 3.38/0.87    inference(subsumption_resolution,[],[f745,f120])).
% 3.38/0.87  fof(f745,plain,(
% 3.38/0.87    ( ! [X0] : (~v4_orders_2(sK5(sK0,sK1,X0)) | ~v7_waybel_0(sK5(sK0,sK1,X0)) | ~l1_waybel_0(sK5(sK0,sK1,X0),sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10)),
% 3.38/0.87    inference(subsumption_resolution,[],[f744,f150])).
% 3.38/0.87  fof(f744,plain,(
% 3.38/0.87    ( ! [X0] : (~v4_orders_2(sK5(sK0,sK1,X0)) | ~v7_waybel_0(sK5(sK0,sK1,X0)) | ~l1_waybel_0(sK5(sK0,sK1,X0),sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_10)),
% 3.38/0.87    inference(subsumption_resolution,[],[f743,f140])).
% 3.38/0.87  fof(f743,plain,(
% 3.38/0.87    ( ! [X0] : (~v4_orders_2(sK5(sK0,sK1,X0)) | ~v7_waybel_0(sK5(sK0,sK1,X0)) | ~l1_waybel_0(sK5(sK0,sK1,X0),sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_10)),
% 3.38/0.87    inference(subsumption_resolution,[],[f742,f135])).
% 3.38/0.87  fof(f742,plain,(
% 3.38/0.87    ( ! [X0] : (~v4_orders_2(sK5(sK0,sK1,X0)) | ~v7_waybel_0(sK5(sK0,sK1,X0)) | ~l1_waybel_0(sK5(sK0,sK1,X0),sK0) | k1_xboole_0 = k10_yellow_6(sK0,sK5(sK0,sK1,X0)) | v2_struct_0(sK5(sK0,sK1,X0)) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_10)),
% 3.38/0.87    inference(resolution,[],[f712,f104])).
% 3.38/0.87  fof(f712,plain,(
% 3.38/0.87    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_xboole_0 = k10_yellow_6(sK0,X0) | v2_struct_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_10)),
% 3.38/0.87    inference(resolution,[],[f154,f110])).
% 3.38/0.87  fof(f110,plain,(
% 3.38/0.87    ( ! [X9] : (v3_yellow_6(X9,sK0) | ~v4_orders_2(X9) | ~v7_waybel_0(X9) | ~l1_waybel_0(X9,sK0) | k1_xboole_0 = k10_yellow_6(sK0,X9) | v2_struct_0(X9)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 3.38/0.87    inference(subsumption_resolution,[],[f109,f93])).
% 3.38/0.87  fof(f109,plain,(
% 3.38/0.87    ( ! [X9] : (~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v4_orders_2(X9) | ~v7_waybel_0(X9) | ~l1_waybel_0(X9,sK0) | k1_xboole_0 = k10_yellow_6(sK0,X9) | v3_yellow_6(X9,sK0)) ) | (spl7_1 | ~spl7_2)),
% 3.38/0.87    inference(subsumption_resolution,[],[f99,f83])).
% 3.38/0.87  fof(f99,plain,(
% 3.38/0.87    ( ! [X9] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v4_orders_2(X9) | ~v7_waybel_0(X9) | ~l1_waybel_0(X9,sK0) | k1_xboole_0 = k10_yellow_6(sK0,X9) | v3_yellow_6(X9,sK0)) ) | ~spl7_2),
% 3.38/0.87    inference(resolution,[],[f88,f57])).
% 3.38/0.87  fof(f57,plain,(
% 3.38/0.87    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0)) )),
% 3.38/0.87    inference(cnf_transformation,[],[f23])).
% 3.38/0.87  fof(f154,plain,(
% 3.38/0.87    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) ) | ~spl7_10),
% 3.38/0.87    inference(avatar_component_clause,[],[f153])).
% 3.38/0.87  fof(f153,plain,(
% 3.38/0.87    spl7_10 <=> ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 3.38/0.87  fof(f1165,plain,(
% 3.38/0.87    ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),k1_zfmisc_1(sK4(sK0,sK1))) | spl7_67),
% 3.38/0.87    inference(avatar_component_clause,[],[f1163])).
% 3.38/0.87  fof(f1163,plain,(
% 3.38/0.87    spl7_67 <=> m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),k1_zfmisc_1(sK4(sK0,sK1)))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 3.38/0.87  fof(f1540,plain,(
% 3.38/0.87    spl7_1 | ~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | spl7_93),
% 3.38/0.87    inference(avatar_contradiction_clause,[],[f1539])).
% 3.38/0.87  fof(f1539,plain,(
% 3.38/0.87    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1538,f83])).
% 3.38/0.87  fof(f1538,plain,(
% 3.38/0.87    v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1537,f241])).
% 3.38/0.87  fof(f1537,plain,(
% 3.38/0.87    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_20 | ~spl7_21 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1536,f245])).
% 3.38/0.87  fof(f1536,plain,(
% 3.38/0.87    ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_21 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1535,f249])).
% 3.38/0.87  fof(f1535,plain,(
% 3.38/0.87    ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_18 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1534,f237])).
% 3.38/0.87  fof(f1534,plain,(
% 3.38/0.87    v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1533,f93])).
% 3.38/0.87  fof(f1533,plain,(
% 3.38/0.87    ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | (~spl7_2 | spl7_93)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1530,f88])).
% 3.38/0.87  fof(f1530,plain,(
% 3.38/0.87    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | v2_struct_0(sK0) | spl7_93),
% 3.38/0.87    inference(resolution,[],[f1526,f67])).
% 3.38/0.87  fof(f67,plain,(
% 3.38/0.87    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 3.38/0.87    inference(cnf_transformation,[],[f33])).
% 3.38/0.87  fof(f33,plain,(
% 3.38/0.87    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.38/0.87    inference(flattening,[],[f32])).
% 3.38/0.87  fof(f32,plain,(
% 3.38/0.87    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.38/0.87    inference(ennf_transformation,[],[f8])).
% 3.38/0.87  fof(f8,axiom,(
% 3.38/0.87    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.38/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 3.38/0.87  fof(f1526,plain,(
% 3.38/0.87    ~m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_93),
% 3.38/0.87    inference(avatar_component_clause,[],[f1524])).
% 3.38/0.87  fof(f1524,plain,(
% 3.38/0.87    spl7_93 <=> m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).
% 3.38/0.87  fof(f1527,plain,(
% 3.38/0.87    ~spl7_93 | spl7_85),
% 3.38/0.87    inference(avatar_split_clause,[],[f1471,f1452,f1524])).
% 3.38/0.87  fof(f1452,plain,(
% 3.38/0.87    spl7_85 <=> r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),u1_struct_0(sK0))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 3.38/0.87  fof(f1471,plain,(
% 3.38/0.87    ~m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_85),
% 3.38/0.87    inference(resolution,[],[f1454,f75])).
% 3.38/0.87  fof(f75,plain,(
% 3.38/0.87    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.38/0.87    inference(cnf_transformation,[],[f4])).
% 3.38/0.87  fof(f4,axiom,(
% 3.38/0.87    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.38/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.38/0.87  fof(f1454,plain,(
% 3.38/0.87    ~r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),u1_struct_0(sK0)) | spl7_85),
% 3.38/0.87    inference(avatar_component_clause,[],[f1452])).
% 3.38/0.87  fof(f1455,plain,(
% 3.38/0.87    spl7_84 | ~spl7_85 | ~spl7_73),
% 3.38/0.87    inference(avatar_split_clause,[],[f1271,f1233,f1452,f1448])).
% 3.38/0.87  fof(f1233,plain,(
% 3.38/0.87    spl7_73 <=> ! [X2] : (~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 3.38/0.87  fof(f1271,plain,(
% 3.38/0.87    ~r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),u1_struct_0(sK0)) | r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0) | ~spl7_73),
% 3.38/0.87    inference(resolution,[],[f1240,f72])).
% 3.38/0.87  fof(f72,plain,(
% 3.38/0.87    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.38/0.87    inference(cnf_transformation,[],[f34])).
% 3.38/0.87  fof(f34,plain,(
% 3.38/0.87    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.38/0.87    inference(ennf_transformation,[],[f1])).
% 3.38/0.87  fof(f1,axiom,(
% 3.38/0.87    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.38/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.38/0.87  fof(f1240,plain,(
% 3.38/0.87    ( ! [X0] : (~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl7_73),
% 3.38/0.87    inference(resolution,[],[f1234,f74])).
% 3.38/0.87  fof(f74,plain,(
% 3.38/0.87    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.38/0.87    inference(cnf_transformation,[],[f4])).
% 3.38/0.87  fof(f1234,plain,(
% 3.38/0.87    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2)) ) | ~spl7_73),
% 3.38/0.87    inference(avatar_component_clause,[],[f1233])).
% 3.38/0.87  fof(f1239,plain,(
% 3.38/0.87    spl7_73 | spl7_74 | ~spl7_22 | ~spl7_26),
% 3.38/0.87    inference(avatar_split_clause,[],[f465,f348,f252,f1236,f1233])).
% 3.38/0.87  fof(f252,plain,(
% 3.38/0.87    spl7_22 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0)))))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 3.38/0.87  fof(f348,plain,(
% 3.38/0.87    spl7_26 <=> ! [X0] : (~r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0))) | k10_yellow_6(sK0,sK3(sK0)) = X0)),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 3.38/0.87  fof(f465,plain,(
% 3.38/0.87    ( ! [X2] : (k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) | ~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_22 | ~spl7_26)),
% 3.38/0.87    inference(forward_demodulation,[],[f453,f438])).
% 3.38/0.87  fof(f438,plain,(
% 3.38/0.87    k1_xboole_0 = k10_yellow_6(sK0,sK3(sK0)) | ~spl7_26),
% 3.38/0.87    inference(resolution,[],[f383,f48])).
% 3.38/0.87  fof(f383,plain,(
% 3.38/0.87    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k10_yellow_6(sK0,sK3(sK0)))) | k10_yellow_6(sK0,sK3(sK0)) = X0) ) | ~spl7_26),
% 3.38/0.87    inference(resolution,[],[f349,f75])).
% 3.38/0.87  fof(f349,plain,(
% 3.38/0.87    ( ! [X0] : (~r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0))) | k10_yellow_6(sK0,sK3(sK0)) = X0) ) | ~spl7_26),
% 3.38/0.87    inference(avatar_component_clause,[],[f348])).
% 3.38/0.87  fof(f453,plain,(
% 3.38/0.87    ( ! [X2] : (~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),X2) | k10_yellow_6(sK0,sK3(sK0)) = k10_yellow_6(sK0,sK2(sK3(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_22 | ~spl7_26)),
% 3.38/0.87    inference(backward_demodulation,[],[f385,f438])).
% 3.38/0.87  fof(f385,plain,(
% 3.38/0.87    ( ! [X2] : (k10_yellow_6(sK0,sK3(sK0)) = k10_yellow_6(sK0,sK2(sK3(sK0))) | ~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k10_yellow_6(sK0,sK3(sK0))),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_22 | ~spl7_26)),
% 3.38/0.87    inference(resolution,[],[f349,f326])).
% 3.38/0.87  fof(f326,plain,(
% 3.38/0.87    ( ! [X0,X1] : (r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),X1) | ~r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_22),
% 3.38/0.87    inference(resolution,[],[f314,f72])).
% 3.38/0.87  fof(f314,plain,(
% 3.38/0.87    ( ! [X0,X1] : (~r2_hidden(X0,k10_yellow_6(sK0,sK2(sK3(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1)) ) | ~spl7_22),
% 3.38/0.87    inference(resolution,[],[f253,f77])).
% 3.38/0.87  fof(f77,plain,(
% 3.38/0.87    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.38/0.87    inference(cnf_transformation,[],[f37])).
% 3.38/0.87  fof(f37,plain,(
% 3.38/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.38/0.87    inference(flattening,[],[f36])).
% 3.38/0.87  fof(f36,plain,(
% 3.38/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.38/0.87    inference(ennf_transformation,[],[f5])).
% 3.38/0.87  fof(f5,axiom,(
% 3.38/0.87    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.38/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 3.38/0.87  fof(f253,plain,(
% 3.38/0.87    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0))))) ) | ~spl7_22),
% 3.38/0.87    inference(avatar_component_clause,[],[f252])).
% 3.38/0.87  fof(f1166,plain,(
% 3.38/0.87    ~spl7_67 | spl7_51),
% 3.38/0.87    inference(avatar_split_clause,[],[f1051,f1038,f1163])).
% 3.38/0.87  fof(f1038,plain,(
% 3.38/0.87    spl7_51 <=> r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1))),
% 3.38/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 3.38/0.87  fof(f1051,plain,(
% 3.38/0.87    ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),k1_zfmisc_1(sK4(sK0,sK1))) | spl7_51),
% 3.38/0.87    inference(resolution,[],[f1040,f75])).
% 3.38/0.87  fof(f1040,plain,(
% 3.38/0.87    ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | spl7_51),
% 3.38/0.87    inference(avatar_component_clause,[],[f1038])).
% 3.38/0.87  fof(f1041,plain,(
% 3.38/0.87    ~spl7_51 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11),
% 3.38/0.87    inference(avatar_split_clause,[],[f1028,f157,f148,f138,f133,f118,f114,f91,f86,f81,f1038])).
% 3.38/0.87  fof(f1028,plain,(
% 3.38/0.87    ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1027,f150])).
% 3.38/0.87  fof(f1027,plain,(
% 3.38/0.87    ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1026,f140])).
% 3.38/0.87  fof(f1026,plain,(
% 3.38/0.87    ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1025,f135])).
% 3.38/0.87  fof(f1025,plain,(
% 3.38/0.87    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 3.38/0.87    inference(subsumption_resolution,[],[f1024,f120])).
% 3.38/0.87  fof(f1024,plain,(
% 3.38/0.87    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 3.38/0.87    inference(duplicate_literal_removal,[],[f1021])).
% 3.38/0.87  fof(f1021,plain,(
% 3.38/0.87    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))),sK4(sK0,sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 3.38/0.87    inference(resolution,[],[f893,f158])).
% 3.38/0.87  fof(f893,plain,(
% 3.38/0.87    ( ! [X0] : (~r3_waybel_9(sK0,sK1,sK4(sK0,X0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r1_tarski(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X0))),sK4(sK0,X0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 3.38/0.87    inference(resolution,[],[f798,f74])).
% 3.38/0.87  fof(f798,plain,(
% 3.38/0.87    ( ! [X2] : (~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2))) | ~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 3.38/0.87    inference(subsumption_resolution,[],[f797,f115])).
% 3.38/0.87  fof(f797,plain,(
% 3.38/0.87    ( ! [X2] : (~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2))) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 3.38/0.87    inference(subsumption_resolution,[],[f796,f83])).
% 3.38/0.87  fof(f796,plain,(
% 3.38/0.87    ( ! [X2] : (~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2))) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 3.38/0.87    inference(subsumption_resolution,[],[f795,f93])).
% 3.38/0.87  fof(f795,plain,(
% 3.38/0.87    ( ! [X2] : (~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2))) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 3.38/0.87    inference(subsumption_resolution,[],[f794,f88])).
% 4.00/0.87  fof(f794,plain,(
% 4.00/0.87    ( ! [X2] : (~r3_waybel_9(sK0,sK1,sK4(sK0,X2)) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,X2))),k1_zfmisc_1(sK4(sK0,X2))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 4.00/0.87    inference(resolution,[],[f711,f51])).
% 4.00/0.87  fof(f711,plain,(
% 4.00/0.87    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 4.00/0.87    inference(subsumption_resolution,[],[f710,f135])).
% 4.00/0.87  fof(f710,plain,(
% 4.00/0.87    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | ~v4_orders_2(sK1) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_5 | ~spl7_7 | ~spl7_9)),
% 4.00/0.87    inference(subsumption_resolution,[],[f709,f120])).
% 4.00/0.87  fof(f709,plain,(
% 4.00/0.87    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_9)),
% 4.00/0.87    inference(subsumption_resolution,[],[f705,f140])).
% 4.00/0.87  fof(f705,plain,(
% 4.00/0.87    ( ! [X2] : (~v7_waybel_0(sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,sK1,X2)),k1_zfmisc_1(X2))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_9)),
% 4.00/0.87    inference(resolution,[],[f150,f215])).
% 4.00/0.87  fof(f215,plain,(
% 4.00/0.87    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~m1_subset_1(k10_yellow_6(sK0,sK5(sK0,X0,X1)),k1_zfmisc_1(X1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 4.00/0.87    inference(resolution,[],[f189,f75])).
% 4.00/0.87  fof(f189,plain,(
% 4.00/0.87    ( ! [X0,X1] : (~r1_tarski(k10_yellow_6(sK0,sK5(sK0,X0,X1)),X1) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 4.00/0.87    inference(resolution,[],[f106,f76])).
% 4.00/0.87  fof(f106,plain,(
% 4.00/0.87    ( ! [X6,X5] : (r2_hidden(X6,k10_yellow_6(sK0,sK5(sK0,X5,X6))) | ~v4_orders_2(X5) | ~v7_waybel_0(X5) | ~l1_waybel_0(X5,sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X5,X6) | v2_struct_0(X5)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 4.00/0.87    inference(subsumption_resolution,[],[f105,f93])).
% 4.00/0.87  fof(f105,plain,(
% 4.00/0.87    ( ! [X6,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X5) | ~v4_orders_2(X5) | ~v7_waybel_0(X5) | ~l1_waybel_0(X5,sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X5,X6) | r2_hidden(X6,k10_yellow_6(sK0,sK5(sK0,X5,X6)))) ) | (spl7_1 | ~spl7_2)),
% 4.00/0.87    inference(subsumption_resolution,[],[f97,f83])).
% 4.00/0.87  fof(f97,plain,(
% 4.00/0.87    ( ! [X6,X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X5) | ~v4_orders_2(X5) | ~v7_waybel_0(X5) | ~l1_waybel_0(X5,sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X5,X6) | r2_hidden(X6,k10_yellow_6(sK0,sK5(sK0,X5,X6)))) ) | ~spl7_2),
% 4.00/0.87    inference(resolution,[],[f88,f61])).
% 4.00/0.87  fof(f61,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))) )),
% 4.00/0.87    inference(cnf_transformation,[],[f27])).
% 4.00/0.87  fof(f718,plain,(
% 4.00/0.87    spl7_4 | spl7_44),
% 4.00/0.87    inference(avatar_split_clause,[],[f39,f716,f114])).
% 4.00/0.87  fof(f39,plain,(
% 4.00/0.87    ( ! [X1] : (v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | v3_yellow_6(sK2(X1),sK0) | v1_compts_1(sK0)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f18])).
% 4.00/0.87  fof(f18,plain,(
% 4.00/0.87    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.00/0.87    inference(flattening,[],[f17])).
% 4.00/0.87  fof(f17,plain,(
% 4.00/0.87    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.00/0.87    inference(ennf_transformation,[],[f16])).
% 4.00/0.87  fof(f16,negated_conjecture,(
% 4.00/0.87    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 4.00/0.87    inference(negated_conjecture,[],[f15])).
% 4.00/0.87  fof(f15,conjecture,(
% 4.00/0.87    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 4.00/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 4.00/0.87  fof(f491,plain,(
% 4.00/0.87    spl7_36 | spl7_37 | ~spl7_13),
% 4.00/0.87    inference(avatar_split_clause,[],[f426,f168,f488,f485])).
% 4.00/0.87  fof(f168,plain,(
% 4.00/0.87    spl7_13 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))))),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 4.00/0.87  fof(f426,plain,(
% 4.00/0.87    ( ! [X2] : (r2_hidden(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,X2)) ) | ~spl7_13),
% 4.00/0.87    inference(duplicate_literal_removal,[],[f423])).
% 4.00/0.87  fof(f423,plain,(
% 4.00/0.87    ( ! [X2] : (r2_hidden(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,X2) | r1_tarski(k1_xboole_0,X2)) ) | ~spl7_13),
% 4.00/0.87    inference(superposition,[],[f72,f393])).
% 4.00/0.87  fof(f393,plain,(
% 4.00/0.87    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl7_13),
% 4.00/0.87    inference(resolution,[],[f389,f72])).
% 4.00/0.88  fof(f389,plain,(
% 4.00/0.88    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | k1_xboole_0 = X5) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f356,f48])).
% 4.00/0.88  fof(f356,plain,(
% 4.00/0.88    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | k1_xboole_0 = X1 | ~r2_hidden(X1,X2)) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f341,f77])).
% 4.00/0.88  fof(f341,plain,(
% 4.00/0.88    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f336,f75])).
% 4.00/0.88  fof(f336,plain,(
% 4.00/0.88    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl7_13),
% 4.00/0.88    inference(subsumption_resolution,[],[f335,f70])).
% 4.00/0.88  fof(f335,plain,(
% 4.00/0.88    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 | r1_tarski(k1_xboole_0,X0)) ) | ~spl7_13),
% 4.00/0.88    inference(subsumption_resolution,[],[f332,f48])).
% 4.00/0.88  fof(f332,plain,(
% 4.00/0.88    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 | r1_tarski(k1_xboole_0,X0)) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f279,f72])).
% 4.00/0.88  fof(f279,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~r2_hidden(sK6(k1_xboole_0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f261,f70])).
% 4.00/0.88  fof(f261,plain,(
% 4.00/0.88    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,X1) | ~r2_hidden(sK6(k1_xboole_0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f234,f72])).
% 4.00/0.88  fof(f234,plain,(
% 4.00/0.88    ( ! [X8,X7] : (~r2_hidden(X7,k1_xboole_0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X7,X8)) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f218,f48])).
% 4.00/0.88  fof(f218,plain,(
% 4.00/0.88    ( ! [X6,X4,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k10_yellow_6(sK0,sK3(sK0)))) | ~r2_hidden(X4,X6) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X4,X5)) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f207,f75])).
% 4.00/0.88  fof(f207,plain,(
% 4.00/0.88    ( ! [X4,X2,X3] : (~r1_tarski(X4,k10_yellow_6(sK0,sK3(sK0))) | ~r2_hidden(X3,X2) | ~r2_hidden(X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f204,f71])).
% 4.00/0.88  fof(f71,plain,(
% 4.00/0.88    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f34])).
% 4.00/0.88  fof(f204,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1)) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f169,f77])).
% 4.00/0.88  fof(f169,plain,(
% 4.00/0.88    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0)))) ) | ~spl7_13),
% 4.00/0.88    inference(avatar_component_clause,[],[f168])).
% 4.00/0.88  fof(f378,plain,(
% 4.00/0.88    ~spl7_14 | ~spl7_15 | spl7_12 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_8 | spl7_27),
% 4.00/0.88    inference(avatar_split_clause,[],[f364,f351,f143,f91,f86,f81,f164,f175,f171])).
% 4.00/0.88  fof(f351,plain,(
% 4.00/0.88    spl7_27 <=> m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.00/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 4.00/0.88  fof(f364,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_8 | spl7_27)),
% 4.00/0.88    inference(subsumption_resolution,[],[f363,f83])).
% 4.00/0.88  fof(f363,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_8 | spl7_27)),
% 4.00/0.88    inference(subsumption_resolution,[],[f362,f145])).
% 4.00/0.88  fof(f362,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_27)),
% 4.00/0.88    inference(subsumption_resolution,[],[f361,f93])).
% 4.00/0.88  fof(f361,plain,(
% 4.00/0.88    ~l1_pre_topc(sK0) | v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK0) | (~spl7_2 | spl7_27)),
% 4.00/0.88    inference(subsumption_resolution,[],[f358,f88])).
% 4.00/0.88  fof(f358,plain,(
% 4.00/0.88    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK0) | spl7_27),
% 4.00/0.88    inference(resolution,[],[f353,f67])).
% 4.00/0.88  fof(f353,plain,(
% 4.00/0.88    ~m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_27),
% 4.00/0.88    inference(avatar_component_clause,[],[f351])).
% 4.00/0.88  fof(f354,plain,(
% 4.00/0.88    spl7_26 | ~spl7_27 | ~spl7_13),
% 4.00/0.88    inference(avatar_split_clause,[],[f331,f168,f351,f348])).
% 4.00/0.88  fof(f331,plain,(
% 4.00/0.88    ( ! [X0] : (~m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0))) | k10_yellow_6(sK0,sK3(sK0)) = X0) ) | ~spl7_13),
% 4.00/0.88    inference(subsumption_resolution,[],[f328,f70])).
% 4.00/0.88  fof(f328,plain,(
% 4.00/0.88    ( ! [X0] : (~m1_subset_1(k10_yellow_6(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0))) | k10_yellow_6(sK0,sK3(sK0)) = X0 | r1_tarski(k10_yellow_6(sK0,sK3(sK0)),X0)) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f230,f72])).
% 4.00/0.88  fof(f230,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~r2_hidden(sK6(k10_yellow_6(sK0,sK3(sK0)),X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k10_yellow_6(sK0,sK3(sK0))) | k10_yellow_6(sK0,sK3(sK0)) = X0) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f206,f70])).
% 4.00/0.88  fof(f206,plain,(
% 4.00/0.88    ( ! [X0,X1] : (r1_tarski(k10_yellow_6(sK0,sK3(sK0)),X1) | ~r2_hidden(sK6(k10_yellow_6(sK0,sK3(sK0)),X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_13),
% 4.00/0.88    inference(resolution,[],[f204,f72])).
% 4.00/0.88  fof(f312,plain,(
% 4.00/0.88    ~spl7_14 | ~spl7_15 | spl7_12 | spl7_1 | spl7_4 | ~spl7_8 | ~spl7_18 | ~spl7_24),
% 4.00/0.88    inference(avatar_split_clause,[],[f311,f264,f236,f143,f114,f81,f164,f175,f171])).
% 4.00/0.88  fof(f311,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | (spl7_1 | spl7_4 | ~spl7_8 | ~spl7_18 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f310,f83])).
% 4.00/0.88  fof(f310,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | v2_struct_0(sK0) | (spl7_4 | ~spl7_8 | ~spl7_18 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f309,f265])).
% 4.00/0.88  fof(f309,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl7_4 | ~spl7_8 | ~spl7_18)),
% 4.00/0.88    inference(subsumption_resolution,[],[f308,f145])).
% 4.00/0.88  fof(f308,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl7_4 | ~spl7_18)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f307])).
% 4.00/0.88  fof(f307,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0)) | (spl7_4 | ~spl7_18)),
% 4.00/0.88    inference(resolution,[],[f306,f122])).
% 4.00/0.88  fof(f122,plain,(
% 4.00/0.88    ( ! [X1] : (m2_yellow_6(sK2(X1),sK0,X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | v2_struct_0(X1)) ) | spl7_4),
% 4.00/0.88    inference(subsumption_resolution,[],[f38,f116])).
% 4.00/0.88  fof(f116,plain,(
% 4.00/0.88    ~v1_compts_1(sK0) | spl7_4),
% 4.00/0.88    inference(avatar_component_clause,[],[f114])).
% 4.00/0.88  fof(f38,plain,(
% 4.00/0.88    ( ! [X1] : (v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | m2_yellow_6(sK2(X1),sK0,X1) | v1_compts_1(sK0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f306,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~m2_yellow_6(sK2(sK3(sK0)),X0,X1) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl7_18),
% 4.00/0.88    inference(resolution,[],[f238,f63])).
% 4.00/0.88  fof(f238,plain,(
% 4.00/0.88    v2_struct_0(sK2(sK3(sK0))) | ~spl7_18),
% 4.00/0.88    inference(avatar_component_clause,[],[f236])).
% 4.00/0.88  fof(f304,plain,(
% 4.00/0.88    ~spl7_14 | ~spl7_15 | spl7_12 | spl7_1 | spl7_4 | ~spl7_8 | spl7_21 | ~spl7_24),
% 4.00/0.88    inference(avatar_split_clause,[],[f303,f264,f248,f143,f114,f81,f164,f175,f171])).
% 4.00/0.88  fof(f303,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | (spl7_1 | spl7_4 | ~spl7_8 | spl7_21 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f302,f83])).
% 4.00/0.88  fof(f302,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | v2_struct_0(sK0) | (spl7_4 | ~spl7_8 | spl7_21 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f301,f265])).
% 4.00/0.88  fof(f301,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl7_4 | ~spl7_8 | spl7_21)),
% 4.00/0.88    inference(subsumption_resolution,[],[f300,f145])).
% 4.00/0.88  fof(f300,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl7_4 | spl7_21)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f299])).
% 4.00/0.88  fof(f299,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0)) | (spl7_4 | spl7_21)),
% 4.00/0.88    inference(resolution,[],[f295,f122])).
% 4.00/0.88  fof(f295,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~m2_yellow_6(sK2(sK3(sK0)),X0,X1) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | spl7_21),
% 4.00/0.88    inference(resolution,[],[f250,f64])).
% 4.00/0.88  fof(f250,plain,(
% 4.00/0.88    ~v4_orders_2(sK2(sK3(sK0))) | spl7_21),
% 4.00/0.88    inference(avatar_component_clause,[],[f248])).
% 4.00/0.88  fof(f293,plain,(
% 4.00/0.88    ~spl7_14 | ~spl7_15 | spl7_12 | spl7_1 | spl7_4 | ~spl7_8 | spl7_20 | ~spl7_24),
% 4.00/0.88    inference(avatar_split_clause,[],[f292,f264,f244,f143,f114,f81,f164,f175,f171])).
% 4.00/0.88  fof(f292,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | (spl7_1 | spl7_4 | ~spl7_8 | spl7_20 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f291,f83])).
% 4.00/0.88  fof(f291,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | v2_struct_0(sK0) | (spl7_4 | ~spl7_8 | spl7_20 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f290,f265])).
% 4.00/0.88  fof(f290,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl7_4 | ~spl7_8 | spl7_20)),
% 4.00/0.88    inference(subsumption_resolution,[],[f289,f145])).
% 4.00/0.88  fof(f289,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl7_4 | spl7_20)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f288])).
% 4.00/0.88  fof(f288,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0)) | (spl7_4 | spl7_20)),
% 4.00/0.88    inference(resolution,[],[f285,f122])).
% 4.00/0.88  fof(f285,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~m2_yellow_6(sK2(sK3(sK0)),X0,X1) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | spl7_20),
% 4.00/0.88    inference(resolution,[],[f246,f65])).
% 4.00/0.88  fof(f246,plain,(
% 4.00/0.88    ~v7_waybel_0(sK2(sK3(sK0))) | spl7_20),
% 4.00/0.88    inference(avatar_component_clause,[],[f244])).
% 4.00/0.88  fof(f284,plain,(
% 4.00/0.88    spl7_12 | ~spl7_14 | ~spl7_15 | spl7_1 | spl7_4 | ~spl7_8 | spl7_19 | ~spl7_24),
% 4.00/0.88    inference(avatar_split_clause,[],[f283,f264,f240,f143,f114,f81,f175,f171,f164])).
% 4.00/0.88  fof(f283,plain,(
% 4.00/0.88    ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | v2_struct_0(sK3(sK0)) | (spl7_1 | spl7_4 | ~spl7_8 | spl7_19 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f282,f145])).
% 4.00/0.88  fof(f282,plain,(
% 4.00/0.88    ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0)) | (spl7_1 | spl7_4 | spl7_19 | ~spl7_24)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f281])).
% 4.00/0.88  fof(f281,plain,(
% 4.00/0.88    ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0)) | (spl7_1 | spl7_4 | spl7_19 | ~spl7_24)),
% 4.00/0.88    inference(resolution,[],[f274,f122])).
% 4.00/0.88  fof(f274,plain,(
% 4.00/0.88    ( ! [X0] : (~m2_yellow_6(sK2(sK3(sK0)),sK0,X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0)) ) | (spl7_1 | spl7_19 | ~spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f256,f265])).
% 4.00/0.88  fof(f256,plain,(
% 4.00/0.88    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(sK2(sK3(sK0)),sK0,X0)) ) | (spl7_1 | spl7_19)),
% 4.00/0.88    inference(subsumption_resolution,[],[f255,f83])).
% 4.00/0.88  fof(f255,plain,(
% 4.00/0.88    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(sK2(sK3(sK0)),sK0,X0) | v2_struct_0(sK0)) ) | spl7_19),
% 4.00/0.88    inference(resolution,[],[f242,f66])).
% 4.00/0.88  fof(f242,plain,(
% 4.00/0.88    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | spl7_19),
% 4.00/0.88    inference(avatar_component_clause,[],[f240])).
% 4.00/0.88  fof(f273,plain,(
% 4.00/0.88    ~spl7_3 | spl7_24),
% 4.00/0.88    inference(avatar_contradiction_clause,[],[f272])).
% 4.00/0.88  fof(f272,plain,(
% 4.00/0.88    $false | (~spl7_3 | spl7_24)),
% 4.00/0.88    inference(subsumption_resolution,[],[f271,f93])).
% 4.00/0.88  fof(f271,plain,(
% 4.00/0.88    ~l1_pre_topc(sK0) | spl7_24),
% 4.00/0.88    inference(resolution,[],[f266,f49])).
% 4.00/0.88  fof(f49,plain,(
% 4.00/0.88    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f19])).
% 4.00/0.88  fof(f19,plain,(
% 4.00/0.88    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.00/0.88    inference(ennf_transformation,[],[f7])).
% 4.00/0.88  fof(f7,axiom,(
% 4.00/0.88    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.00/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 4.00/0.88  fof(f266,plain,(
% 4.00/0.88    ~l1_struct_0(sK0) | spl7_24),
% 4.00/0.88    inference(avatar_component_clause,[],[f264])).
% 4.00/0.88  fof(f254,plain,(
% 4.00/0.88    spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | spl7_22 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17),
% 4.00/0.88    inference(avatar_split_clause,[],[f225,f220,f91,f86,f81,f252,f248,f244,f240,f236])).
% 4.00/0.88  fof(f220,plain,(
% 4.00/0.88    spl7_17 <=> ! [X0] : (~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 4.00/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 4.00/0.88  fof(f225,plain,(
% 4.00/0.88    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0)))) | v2_struct_0(sK2(sK3(sK0)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f224])).
% 4.00/0.88  fof(f224,plain,(
% 4.00/0.88    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k10_yellow_6(sK0,sK2(sK3(sK0)))) | v2_struct_0(sK2(sK3(sK0)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17)),
% 4.00/0.88    inference(resolution,[],[f221,f108])).
% 4.00/0.88  fof(f108,plain,(
% 4.00/0.88    ( ! [X8,X7] : (r3_waybel_9(sK0,X7,X8) | ~v4_orders_2(X7) | ~v7_waybel_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_hidden(X8,k10_yellow_6(sK0,X7)) | v2_struct_0(X7)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 4.00/0.88    inference(subsumption_resolution,[],[f107,f93])).
% 4.00/0.88  fof(f107,plain,(
% 4.00/0.88    ( ! [X8,X7] : (~l1_pre_topc(sK0) | v2_struct_0(X7) | ~v4_orders_2(X7) | ~v7_waybel_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_hidden(X8,k10_yellow_6(sK0,X7)) | r3_waybel_9(sK0,X7,X8)) ) | (spl7_1 | ~spl7_2)),
% 4.00/0.88    inference(subsumption_resolution,[],[f98,f83])).
% 4.00/0.88  fof(f98,plain,(
% 4.00/0.88    ( ! [X8,X7] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~v4_orders_2(X7) | ~v7_waybel_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_hidden(X8,k10_yellow_6(sK0,X7)) | r3_waybel_9(sK0,X7,X8)) ) | ~spl7_2),
% 4.00/0.88    inference(resolution,[],[f88,f59])).
% 4.00/0.88  fof(f59,plain,(
% 4.00/0.88    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f25])).
% 4.00/0.88  fof(f25,plain,(
% 4.00/0.88    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.00/0.88    inference(flattening,[],[f24])).
% 4.00/0.88  fof(f24,plain,(
% 4.00/0.88    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.00/0.88    inference(ennf_transformation,[],[f11])).
% 4.00/0.88  fof(f11,axiom,(
% 4.00/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 4.00/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 4.00/0.88  fof(f221,plain,(
% 4.00/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_17),
% 4.00/0.88    inference(avatar_component_clause,[],[f220])).
% 4.00/0.88  fof(f222,plain,(
% 4.00/0.88    spl7_12 | ~spl7_14 | ~spl7_15 | spl7_17 | spl7_4 | ~spl7_8 | ~spl7_16),
% 4.00/0.88    inference(avatar_split_clause,[],[f214,f209,f143,f114,f220,f175,f171,f164])).
% 4.00/0.88  fof(f209,plain,(
% 4.00/0.88    spl7_16 <=> ! [X1,X0] : (~m2_yellow_6(X0,sK0,sK3(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 4.00/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 4.00/0.88  fof(f214,plain,(
% 4.00/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | v2_struct_0(sK3(sK0))) ) | (spl7_4 | ~spl7_8 | ~spl7_16)),
% 4.00/0.88    inference(subsumption_resolution,[],[f212,f145])).
% 4.00/0.88  fof(f212,plain,(
% 4.00/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK3(sK0))) ) | (spl7_4 | ~spl7_16)),
% 4.00/0.88    inference(resolution,[],[f210,f122])).
% 4.00/0.88  fof(f210,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~m2_yellow_6(X0,sK0,sK3(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_16),
% 4.00/0.88    inference(avatar_component_clause,[],[f209])).
% 4.00/0.88  fof(f211,plain,(
% 4.00/0.88    spl7_12 | spl7_16 | ~spl7_14 | ~spl7_15 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_8),
% 4.00/0.88    inference(avatar_split_clause,[],[f188,f143,f114,f91,f86,f81,f175,f171,f209,f164])).
% 4.00/0.88  fof(f188,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~m2_yellow_6(X0,sK0,sK3(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | v2_struct_0(sK3(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_8)),
% 4.00/0.88    inference(subsumption_resolution,[],[f180,f145])).
% 4.00/0.88  fof(f180,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~m2_yellow_6(X0,sK0,sK3(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | v2_struct_0(sK3(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f179])).
% 4.00/0.88  fof(f179,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~m2_yellow_6(X0,sK0,sK3(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | v2_struct_0(sK3(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(resolution,[],[f102,f128])).
% 4.00/0.88  fof(f128,plain,(
% 4.00/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK3(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(subsumption_resolution,[],[f127,f83])).
% 4.00/0.88  fof(f127,plain,(
% 4.00/0.88    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK3(sK0),X0) | v2_struct_0(sK0)) ) | (~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(subsumption_resolution,[],[f126,f93])).
% 4.00/0.88  fof(f126,plain,(
% 4.00/0.88    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK3(sK0),X0) | v2_struct_0(sK0)) ) | (~spl7_2 | spl7_4)),
% 4.00/0.88    inference(subsumption_resolution,[],[f124,f88])).
% 4.00/0.88  fof(f124,plain,(
% 4.00/0.88    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK3(sK0),X0) | v2_struct_0(sK0)) ) | spl7_4),
% 4.00/0.88    inference(resolution,[],[f116,f50])).
% 4.00/0.88  fof(f50,plain,(
% 4.00/0.88    ( ! [X2,X0] : (v1_compts_1(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK3(X0),X2) | v2_struct_0(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f21])).
% 4.00/0.88  fof(f102,plain,(
% 4.00/0.88    ( ! [X2,X0,X1] : (r3_waybel_9(sK0,X0,X2) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(X1,sK0,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X1,X2) | v2_struct_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 4.00/0.88    inference(subsumption_resolution,[],[f101,f93])).
% 4.00/0.88  fof(f101,plain,(
% 4.00/0.88    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(X1,sK0,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X1,X2) | r3_waybel_9(sK0,X0,X2)) ) | (spl7_1 | ~spl7_2)),
% 4.00/0.88    inference(subsumption_resolution,[],[f95,f83])).
% 4.00/0.88  fof(f95,plain,(
% 4.00/0.88    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(X1,sK0,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X1,X2) | r3_waybel_9(sK0,X0,X2)) ) | ~spl7_2),
% 4.00/0.88    inference(resolution,[],[f88,f62])).
% 4.00/0.88  fof(f62,plain,(
% 4.00/0.88    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X3) | r3_waybel_9(X0,X1,X3)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f29])).
% 4.00/0.88  fof(f29,plain,(
% 4.00/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.00/0.88    inference(flattening,[],[f28])).
% 4.00/0.88  fof(f28,plain,(
% 4.00/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.00/0.88    inference(ennf_transformation,[],[f12])).
% 4.00/0.88  fof(f12,axiom,(
% 4.00/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 4.00/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).
% 4.00/0.88  fof(f203,plain,(
% 4.00/0.88    spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_12),
% 4.00/0.88    inference(avatar_contradiction_clause,[],[f202])).
% 4.00/0.88  fof(f202,plain,(
% 4.00/0.88    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_12)),
% 4.00/0.88    inference(subsumption_resolution,[],[f201,f116])).
% 4.00/0.88  fof(f201,plain,(
% 4.00/0.88    v1_compts_1(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12)),
% 4.00/0.88    inference(subsumption_resolution,[],[f200,f83])).
% 4.00/0.88  fof(f200,plain,(
% 4.00/0.88    v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_12)),
% 4.00/0.88    inference(subsumption_resolution,[],[f199,f93])).
% 4.00/0.88  fof(f199,plain,(
% 4.00/0.88    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl7_2 | ~spl7_12)),
% 4.00/0.88    inference(subsumption_resolution,[],[f197,f88])).
% 4.00/0.88  fof(f197,plain,(
% 4.00/0.88    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl7_12),
% 4.00/0.88    inference(resolution,[],[f166,f53])).
% 4.00/0.88  fof(f53,plain,(
% 4.00/0.88    ( ! [X0] : (~v2_struct_0(sK3(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f21])).
% 4.00/0.88  fof(f166,plain,(
% 4.00/0.88    v2_struct_0(sK3(sK0)) | ~spl7_12),
% 4.00/0.88    inference(avatar_component_clause,[],[f164])).
% 4.00/0.88  fof(f196,plain,(
% 4.00/0.88    spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | spl7_15),
% 4.00/0.88    inference(avatar_contradiction_clause,[],[f195])).
% 4.00/0.88  fof(f195,plain,(
% 4.00/0.88    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | spl7_15)),
% 4.00/0.88    inference(subsumption_resolution,[],[f194,f116])).
% 4.00/0.88  fof(f194,plain,(
% 4.00/0.88    v1_compts_1(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_15)),
% 4.00/0.88    inference(subsumption_resolution,[],[f193,f83])).
% 4.00/0.88  fof(f193,plain,(
% 4.00/0.88    v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl7_2 | ~spl7_3 | spl7_15)),
% 4.00/0.88    inference(subsumption_resolution,[],[f192,f93])).
% 4.00/0.88  fof(f192,plain,(
% 4.00/0.88    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl7_2 | spl7_15)),
% 4.00/0.88    inference(subsumption_resolution,[],[f190,f88])).
% 4.00/0.88  fof(f190,plain,(
% 4.00/0.88    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | spl7_15),
% 4.00/0.88    inference(resolution,[],[f177,f54])).
% 4.00/0.88  fof(f54,plain,(
% 4.00/0.88    ( ! [X0] : (v4_orders_2(sK3(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f21])).
% 4.00/0.88  fof(f177,plain,(
% 4.00/0.88    ~v4_orders_2(sK3(sK0)) | spl7_15),
% 4.00/0.88    inference(avatar_component_clause,[],[f175])).
% 4.00/0.88  fof(f187,plain,(
% 4.00/0.88    spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | spl7_14),
% 4.00/0.88    inference(avatar_contradiction_clause,[],[f186])).
% 4.00/0.88  fof(f186,plain,(
% 4.00/0.88    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | spl7_14)),
% 4.00/0.88    inference(subsumption_resolution,[],[f185,f116])).
% 4.00/0.88  fof(f185,plain,(
% 4.00/0.88    v1_compts_1(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_14)),
% 4.00/0.88    inference(subsumption_resolution,[],[f184,f83])).
% 4.00/0.88  fof(f184,plain,(
% 4.00/0.88    v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl7_2 | ~spl7_3 | spl7_14)),
% 4.00/0.88    inference(subsumption_resolution,[],[f183,f93])).
% 4.00/0.88  fof(f183,plain,(
% 4.00/0.88    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl7_2 | spl7_14)),
% 4.00/0.88    inference(subsumption_resolution,[],[f181,f88])).
% 4.00/0.88  fof(f181,plain,(
% 4.00/0.88    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | spl7_14),
% 4.00/0.88    inference(resolution,[],[f173,f55])).
% 4.00/0.88  fof(f55,plain,(
% 4.00/0.88    ( ! [X0] : (v7_waybel_0(sK3(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f21])).
% 4.00/0.88  fof(f173,plain,(
% 4.00/0.88    ~v7_waybel_0(sK3(sK0)) | spl7_14),
% 4.00/0.88    inference(avatar_component_clause,[],[f171])).
% 4.00/0.88  fof(f178,plain,(
% 4.00/0.88    spl7_12 | spl7_13 | ~spl7_14 | ~spl7_15 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_8),
% 4.00/0.88    inference(avatar_split_clause,[],[f162,f143,f114,f91,f86,f81,f175,f171,f168,f164])).
% 4.00/0.88  fof(f162,plain,(
% 4.00/0.88    ( ! [X0] : (~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))) | v2_struct_0(sK3(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_8)),
% 4.00/0.88    inference(subsumption_resolution,[],[f161,f145])).
% 4.00/0.88  fof(f161,plain,(
% 4.00/0.88    ( ! [X0] : (~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))) | v2_struct_0(sK3(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(duplicate_literal_removal,[],[f160])).
% 4.00/0.88  fof(f160,plain,(
% 4.00/0.88    ( ! [X0] : (~v4_orders_2(sK3(sK0)) | ~v7_waybel_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK3(sK0))) | v2_struct_0(sK3(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(resolution,[],[f108,f128])).
% 4.00/0.88  fof(f159,plain,(
% 4.00/0.88    ~spl7_4 | spl7_11 | spl7_1 | ~spl7_2 | ~spl7_3),
% 4.00/0.88    inference(avatar_split_clause,[],[f112,f91,f86,f81,f157,f114])).
% 4.00/0.88  fof(f112,plain,(
% 4.00/0.88    ( ! [X10] : (v2_struct_0(X10) | ~v4_orders_2(X10) | ~v7_waybel_0(X10) | ~l1_waybel_0(X10,sK0) | r3_waybel_9(sK0,X10,sK4(sK0,X10)) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 4.00/0.88    inference(subsumption_resolution,[],[f111,f93])).
% 4.00/0.88  fof(f111,plain,(
% 4.00/0.88    ( ! [X10] : (~l1_pre_topc(sK0) | v2_struct_0(X10) | ~v4_orders_2(X10) | ~v7_waybel_0(X10) | ~l1_waybel_0(X10,sK0) | r3_waybel_9(sK0,X10,sK4(sK0,X10)) | ~v1_compts_1(sK0)) ) | (spl7_1 | ~spl7_2)),
% 4.00/0.88    inference(subsumption_resolution,[],[f100,f83])).
% 4.00/0.88  fof(f100,plain,(
% 4.00/0.88    ( ! [X10] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X10) | ~v4_orders_2(X10) | ~v7_waybel_0(X10) | ~l1_waybel_0(X10,sK0) | r3_waybel_9(sK0,X10,sK4(sK0,X10)) | ~v1_compts_1(sK0)) ) | ~spl7_2),
% 4.00/0.88    inference(resolution,[],[f88,f52])).
% 4.00/0.88  fof(f52,plain,(
% 4.00/0.88    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | r3_waybel_9(X0,X1,sK4(X0,X1)) | ~v1_compts_1(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f21])).
% 4.00/0.88  fof(f155,plain,(
% 4.00/0.88    ~spl7_4 | spl7_10),
% 4.00/0.88    inference(avatar_split_clause,[],[f40,f153,f114])).
% 4.00/0.88  fof(f40,plain,(
% 4.00/0.88    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0) | ~v1_compts_1(sK0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f151,plain,(
% 4.00/0.88    ~spl7_4 | spl7_9),
% 4.00/0.88    inference(avatar_split_clause,[],[f44,f148,f114])).
% 4.00/0.88  fof(f44,plain,(
% 4.00/0.88    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f146,plain,(
% 4.00/0.88    spl7_8 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4),
% 4.00/0.88    inference(avatar_split_clause,[],[f131,f114,f91,f86,f81,f143])).
% 4.00/0.88  fof(f131,plain,(
% 4.00/0.88    l1_waybel_0(sK3(sK0),sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(subsumption_resolution,[],[f130,f83])).
% 4.00/0.88  fof(f130,plain,(
% 4.00/0.88    l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | spl7_4)),
% 4.00/0.88    inference(subsumption_resolution,[],[f129,f93])).
% 4.00/0.88  fof(f129,plain,(
% 4.00/0.88    ~l1_pre_topc(sK0) | l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK0) | (~spl7_2 | spl7_4)),
% 4.00/0.88    inference(subsumption_resolution,[],[f125,f88])).
% 4.00/0.88  fof(f125,plain,(
% 4.00/0.88    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK0) | spl7_4),
% 4.00/0.88    inference(resolution,[],[f116,f56])).
% 4.00/0.88  fof(f56,plain,(
% 4.00/0.88    ( ! [X0] : (v1_compts_1(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | l1_waybel_0(sK3(X0),X0) | v2_struct_0(X0)) )),
% 4.00/0.88    inference(cnf_transformation,[],[f21])).
% 4.00/0.88  fof(f141,plain,(
% 4.00/0.88    ~spl7_4 | spl7_7),
% 4.00/0.88    inference(avatar_split_clause,[],[f43,f138,f114])).
% 4.00/0.88  fof(f43,plain,(
% 4.00/0.88    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f136,plain,(
% 4.00/0.88    ~spl7_4 | spl7_6),
% 4.00/0.88    inference(avatar_split_clause,[],[f42,f133,f114])).
% 4.00/0.88  fof(f42,plain,(
% 4.00/0.88    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f121,plain,(
% 4.00/0.88    ~spl7_4 | ~spl7_5),
% 4.00/0.88    inference(avatar_split_clause,[],[f41,f118,f114])).
% 4.00/0.88  fof(f41,plain,(
% 4.00/0.88    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f94,plain,(
% 4.00/0.88    spl7_3),
% 4.00/0.88    inference(avatar_split_clause,[],[f47,f91])).
% 4.00/0.88  fof(f47,plain,(
% 4.00/0.88    l1_pre_topc(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f89,plain,(
% 4.00/0.88    spl7_2),
% 4.00/0.88    inference(avatar_split_clause,[],[f46,f86])).
% 4.00/0.88  fof(f46,plain,(
% 4.00/0.88    v2_pre_topc(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  fof(f84,plain,(
% 4.00/0.88    ~spl7_1),
% 4.00/0.88    inference(avatar_split_clause,[],[f45,f81])).
% 4.00/0.88  fof(f45,plain,(
% 4.00/0.88    ~v2_struct_0(sK0)),
% 4.00/0.88    inference(cnf_transformation,[],[f18])).
% 4.00/0.88  % SZS output end Proof for theBenchmark
% 4.00/0.88  % (3880)------------------------------
% 4.00/0.88  % (3880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.88  % (3880)Termination reason: Refutation
% 4.00/0.88  
% 4.00/0.88  % (3880)Memory used [KB]: 12920
% 4.00/0.88  % (3880)Time elapsed: 0.451 s
% 4.00/0.88  % (3880)------------------------------
% 4.00/0.88  % (3880)------------------------------
% 4.00/0.88  % (3859)Success in time 0.517 s
%------------------------------------------------------------------------------
